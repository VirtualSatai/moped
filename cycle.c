#include "mcheck.h"
#include "cycle.h"
#include "common.h"

char (*mc_cyclemethod)(CNode);
Head (*mc_edgemethod)(Head*);

void rename_rules(Head head, int* perm, char comp)
{
	Rule rule;
	DdNode *tmp0;
	int thiscomp = head->comp;

	if (mc_verbose) common_resource_setmark(3);

	while (head && (!comp || head->comp == thiscomp))
	{
	    for (rule = head->rules; rule; rule = rule->next)
	    {
		Cudd_Ref(tmp0 = Cudd_bddPermute(mc_mgr,rule->vars,perm));
		Cudd_RecursiveDeref(mc_mgr,rule->vars);
		rule->vars = tmp0;
	    }
	    head = head->stack;
	}

	if (mc_verbose) common_resource_displaymark(3,"rename",NULL);
}

void add_cnode (CNode *first, Head head)
{
	CNode cnode = create_cnode();
	cnode->head = head;
	head->cnode = cnode;
	cnode->bkedges = cnode->fwedges = NULL;
	cnode->next = *first;
	*first = cnode;
}

CEdge add_cedge (CNode from, CNode to, DdNode *bdd, char b)
{
	CEdge edge;

	if (bdd == emptyset) return NULL;

	edge = create_cedge();
	Cudd_Ref(edge->e = bdd);
	edge->b = b;
	edge->from = from;
	edge->to = to;
	edge->nextfrom = to->bkedges;
	edge->nextto = from->fwedges;
	to->bkedges = from->fwedges = edge;
	return edge;
}

void free_cgraph (CNode first)
{
	CNode node;
	CEdge edge;

	while (first)
	{
		node = first;
		first = node->next;
		while (node->fwedges)
		{
			edge = node->fwedges;
			node->fwedges = edge->nextto;
			Cudd_RecursiveDeref(mc_mgr,edge->e);
			free(edge);
		}
		Cudd_RecursiveDeref(mc_mgr,node->z);
		free(node);
	}
}

/*****************************************************************************/

Head find_summary (Head *goalptr)
{
	DdNode *onerep, *zerorep;
	FATransition nt;
	Head goal, cstart = *goalptr, result = NULL;
	CNode snode;
	int thiscomp = cstart->comp;
	char c;

        /* find subset of heads that cover all circles with 1-labelled edges */
	find_cover(cstart);

	/* rename py -> qy'' in all rules involved in cycle search */
	rename_rules(*goalptr,mc_perm3,1);

	for (; *goalptr && (*goalptr)->comp == thiscomp;
			*goalptr = (*goalptr)->stack)
	{
	    goal = *goalptr;

	    if (!goal->lowpt) continue;

	    if (mc_verbose > 1)
		printf("%s %s\n", name_cstring(goal->state),
					  name_cstring(goal->name));

	    /* compute all circles starting from goal via a 1-edge */
	    if (mc_verbose > 1) printf(" one loop\n");
	    onerep = compute_rep(goal,cstart,1);

	    /* compute all circles starting from goal via a 0-edge */
	    if (mc_verbose > 1) printf(" zero loop\n");
	    zerorep = compute_rep(goal,cstart,0);

	    snode = NULL;
	    add_cnode(&snode,goal);
	    add_cedge(snode,snode,onerep,1);
	    add_cedge(snode,snode,zerorep,0);
	    Cudd_RecursiveDeref(mc_mgr,onerep);
	    Cudd_RecursiveDeref(mc_mgr,zerorep);

	    /* eliminate trivially irreversible transitions */
	    if (mc_elimstuff)
	    {
		if (mc_verbose) common_resource_setmark(3);
		eliminate_stuff(snode);
		if (mc_verbose) common_resource_displaymark(3,"flips",NULL);
	    }

	    /* compute the circles within onerep (zerorep+onerep)* */

	    if (mc_verbose > 1) printf(" components\n");
	    if (mc_verbose) common_resource_setmark(3);
	    c = mc_cyclemethod(snode);
	    if (mc_verbose) common_resource_displaymark(3,"find cycles",NULL);

	    if (c)
	    {
		/* We have found some repeating heads. Add a transition to
		   the automaton and store the BDD in the trans field. */
		/* fixme: adjust for el and owcty overapproximation */
		
		if (mc_verbose > 1) printf("%s %s\n",
			name_cstring(goal->state), name_cstring(goal->name));
		if (mc_verbose > 2) print_bdd(snode->z,fatrans_set,
					goal->name,0,0,0);
		if (mc_verbose > 1) printf("====\n");

		if (mc_poststar)
		{
			Cudd_Ref(goal->trans = snode->z);
			result = goal;
			if (mc_poststar && mc_demand) return result;
		}
		else
		{
			Cudd_Ref(snode->z);
			nt = fatrans_table_insert(&mc_trans,
			    fatrans_create(goal->state,goal->name,mc_sstate,0));
			add_bdd_trans(&mc_trans,nt,snode->z,NULL,0);
		}
	    }

	    free_cgraph(snode);
	}

	return result;
}

/*****************************************************************************/

Head find_direct (Head *goalptr)
{
	Head goal, cstart = *goalptr, result = NULL;
	CNode snode, n1;
	FATransition nt;
	Rule rule;
	int thiscomp = cstart->comp;

	/* advance goalptr to start of next component */
	for (; *goalptr && (*goalptr)->comp == thiscomp;
			*goalptr = (*goalptr)->stack);

	/* associate a cnode with every head */
	snode = NULL;
	for (goal = cstart; goal && goal->comp == thiscomp; goal = goal->stack)
	{
		add_cnode(&snode,goal);
	}

	for (goal = cstart; goal && goal->comp == thiscomp; goal = goal->stack)
	{
		for (rule = goal->rules; rule; rule = rule->next)
		{
		    if (rule->head->comp != goal->comp) continue;
		    add_cedge(rule->head->cnode,goal->cnode,rule->vars,rule->b);
		}
	}

	/* eliminate trivially irreversible transitions */
	if (mc_elimstuff)
	{
		if (mc_verbose) common_resource_setmark(3);
		eliminate_stuff(snode);
		if (mc_verbose) common_resource_displaymark(3,"flips",NULL);
	}

	/* compute the circles within onerep (zerorep+onerep)* */

	if (mc_verbose > 1) printf(" components\n");
	if (mc_verbose) common_resource_setmark(3);
	mc_cyclemethod(snode);
	if (mc_verbose) common_resource_displaymark(3,"find cycles",NULL);

	/* Check if We have found some repeating heads. Add a transition to
	   the automaton and store the BDD in the trans field if so. */
		
	for (n1 = snode; n1; n1 = n1->next)
	{
		if (n1->z == emptyset) continue;

		/* EL and OWCTY return overapproximations of the states
		   contained in 1-cycles; we have to check if our states
		   really do have a 1-cycle. */
		if (mc_cyclemethod == el_method
				|| mc_cyclemethod == owcty_method)
		{
			check_for_real_cycles(snode,n1);
			if (n1->z == emptyset) continue;
		}
		
		goal = n1->head;
		if (mc_verbose > 1) printf("%s %s\n",
			name_cstring(goal->state), name_cstring(goal->name));
		if (mc_verbose > 2) print_bdd(n1->z,fatrans_set,
					goal->name,0,0,0);
		if (mc_verbose > 1) printf("====\n");

		if (mc_poststar)
		{
			Cudd_Ref(goal->trans = n1->z);
			result = goal;
			if (mc_poststar && mc_demand) break;
		}
		else
		{
			Cudd_Ref(n1->z);
			nt = fatrans_table_insert(&mc_trans,
			    fatrans_create(goal->state,goal->name,mc_sstate,0));
			add_bdd_trans(&mc_trans,nt,n1->z,NULL,0);
		}
	}

	free_cgraph(snode);
	return result;
}

/*****************************************************************************/

Head find_cycles ()
{
	DdNode *tmp0;
	Head head, h2, goal;
	Rule rule;

        if (mc_cyclemethod == xb_decomp) find_one_init();

        common_resource_setmark(2);

        /* pre* method: get rid of y'' in all rule bdds so they don't get
                        in the way when computing the repeating heads and pre*
           post* method: get rid of y'' only in repeating heads */

        head = mc_poststar? dfs_found : mc_heads.list;
        while (head)
        {
                if (head->comp)
		    for (rule = head->rules; rule; rule = rule->next)
		    {
                        if (!rule->tail) continue;
                        /* rule->vars = ex y'': rule->vars */
                        Cudd_Ref(tmp0 = Cudd_bddExistAbstract
                                (mc_mgr,rule->vars,mc_cube6));
                        Cudd_RecursiveDeref(mc_mgr,rule->vars);
                        rule->vars = tmp0;
		    }

                head = mc_poststar? head->stack : head->list;
        }


	/* search strongly connected components among heads */
	/* only consider transitions within the control-flow sccs */

	head = dfs_found;
	goal = NULL;
	while (head)
	{
		h2 = mc_edgemethod(&head);
		if (h2) goal = h2;
		if (goal && mc_poststar && mc_demand) break;
	}

	common_resource_displaymark(2,"heads",&mctime_head);

	if (mc_edgemethod == find_summary && (!mc_poststar || goal))
		rename_rules(dfs_found,mc_perm2,0);

	return goal;
}
