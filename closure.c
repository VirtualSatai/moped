#include "cycle.h"

void init_y_stack (CNode snode, CNode *cstack)
{
	*cstack = NULL;
	while (snode)
	{
		Cudd_Ref(snode->y = emptyset);
		snode->flag = 0;
		snode = snode->next;
	}
}

void add_y_edge (CNode node, DdNode *e, CNode *cstack)
{
	DdNode *tmp0;

	if (e == emptyset) return;
	
	Cudd_Ref(tmp0 = Cudd_bddOr(mc_mgr,node->y,e));

	if (tmp0 != node->y && !node->flag)
	{
		node->stack = *cstack;
		*cstack = node;
		node->flag = 1;
	}

	Cudd_RecursiveDeref(mc_mgr,node->y);
	Cudd_RecursiveDeref(mc_mgr,e);
	node->y = tmp0;
}

void clear_y_stack (CNode snode)
{
	while (snode)
	{
		Cudd_RecursiveDeref(mc_mgr,snode->y);
		snode = snode->next;
	}
}

char compute_closure (CNode snode)
{
	DdNode *tmp0, *tmp1;
	CNode n1, n2, cstack;
	CEdge edge;
	char retval = 0;

	for (n1 = snode; n1; n1 = n1->next)
		Cudd_Ref(n1->z = emptyset);

	for (n1 = snode; n1; n1 = n1->next)
	{
		init_y_stack(snode,&cstack);

		for (edge = n1->bkedges; edge; edge = edge->nextfrom)
		{
		    if (!edge->b) continue;

		    /* tmp1 = edge->e(py->qy'', p'y'->py) */
		    Cudd_Ref(tmp0 = Cudd_bddPermute(mc_mgr,edge->e,mc_perm3));
		    Cudd_Ref(tmp1 = Cudd_bddPermute(mc_mgr,tmp0,mc_perm1));
		    Cudd_RecursiveDeref(mc_mgr,tmp0);

		    add_y_edge(edge->from,tmp1,&cstack);
		}

		while (cstack)
		{
		    n2 = cstack;
		    n2->flag = 0;
		    cstack = cstack->stack;

		    for (edge = n2->bkedges; edge; edge = edge->nextfrom)
		    {
			/* tmp1 = (ex p,y: edge->e /\ n2->y)(p'y'->py) */
			Cudd_Ref(tmp0 = Cudd_bddAndAbstract
				(mc_mgr,edge->e,n2->y,mc_cube1));
			Cudd_Ref(tmp1 = Cudd_bddPermute
				(mc_mgr,tmp0,mc_perm1));
			Cudd_RecursiveDeref(mc_mgr,tmp0);

			add_y_edge(edge->from,tmp1,&cstack);
		    }
		}

		/* n1->z = ex p',y': n1->y /\ (p=q,y=y'') */
		Cudd_Ref(n1->z = Cudd_bddAndAbstract
			(mc_mgr,n1->y,mc_pyeqv,mc_cube2));
		if (n1->z != emptyset) retval = 1;

		clear_y_stack(snode);

		if (retval && mc_poststar && mc_demand) break;
	}

	return retval;
}
