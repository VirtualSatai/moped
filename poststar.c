/****************************************************************************/
/* poststar.c								    */
/*									    */
/* Computes post* of a pushdown system with BDDs			    */
/*									    */
/* Stefan Schwoon, November/December 2000				    */
/****************************************************************************/

#include "common.h"
#include "mcheck.h"
#include "cycle.h"

#include <string.h>

FATransTable p_trans, p_index;
HeadTable p_heads;

char demand_finished;

void add_post_rel (FATransTable* index, FATransition t, DdNode *newbdd,
			PDSTransition pt)
{
	DdNode *tmp0, *tmp1;
	FATransition thead;
	char oldtrans = t->f & FF_THEAD;

	if (mc_trace)
	{
		OriginList newlist;

		Cudd_Ref(tmp1 = Cudd_bddAnd(mc_mgr,newbdd,Cudd_Not(t->rel)));
		if (tmp1 != emptyset)
		{
		    newlist = common_malloc(sizeof(struct OriginListElement));
		    newlist->pt = pt;
		    newlist->midstate = 0;
		    newlist->bdd = tmp1;
		    newlist->n = mc_age;
		    newlist->next = t->origin;
		    t->origin = newlist;
		}
	}

	Cudd_Ref(tmp0 = Cudd_bddOr(mc_mgr,newbdd,t->rel));
	Cudd_RecursiveDeref(mc_mgr,newbdd);
	Cudd_RecursiveDeref(mc_mgr,t->rel);
	t->rel = tmp0;

	if (oldtrans) return;

	thead = fatrans_table_insert(index,
				fatrans_create(t->from_state,0,0,0));
	t->list = thead->list;
	thead->list = t;
	t->f |= FF_THEAD;
}

void add_eps_rel (FATransTable* index, FATransition t, DdNode *newbdd,
			PDSTransition pt)
{
	DdNode *tmp0, *tmp1;
	FATransition thead;
	char oldtrans = t->f & FF_THEAD;

	if (mc_trace)
	{
		OriginList newlist;

		Cudd_Ref(tmp1 = Cudd_bddAnd(mc_mgr,newbdd,Cudd_Not(t->rel)));
		if (tmp1 == emptyset) return;

		for (newlist = t->origin; newlist; newlist = newlist->next)
		{
			if (newlist->pt != pt) continue;
			Cudd_Ref(tmp0 = Cudd_bddOr(mc_mgr,newbdd,newlist->bdd));
			Cudd_RecursiveDeref(mc_mgr,newlist->bdd);
			newlist->bdd = tmp0;
			break;
		}

		if (!newlist)
		{
		    newlist = common_malloc(sizeof(struct OriginListElement));
		    newlist->pt = pt;
		    newlist->midstate = 0;
		    newlist->bdd = tmp1;
		    newlist->n = mc_age;
		    newlist->next = t->origin;
		    t->origin = newlist;
		}
	}

	Cudd_Ref(tmp0 = Cudd_bddOr(mc_mgr,newbdd,t->rel));
	Cudd_RecursiveDeref(mc_mgr,newbdd);
	Cudd_RecursiveDeref(mc_mgr,t->rel);
	t->rel = tmp0;

	if (oldtrans) return;

	thead = fatrans_table_insert(index,fatrans_create(0,0,t->to_state,0));
	t->list = thead->list;
	thead->list = t;
	t->f |= FF_THEAD;
}

void compute_poststar ()
{
	PDSTransition	pt;
	Head		head, head1, newhead;
	Rule		rule;
	FATransition	nt, t, t1, thead;
	NameStack	stack;
	Name		state1, state2;
	DdNode		*tmp0, *tmp1, *tmp2, *tmp3;
	char		tmpbuf[16];
	int		i;
	int		edgecount = 0;

	common_resource_setmark(2);

	/* initialise auxiliary tables */
	mc_heads = head_table_empty();
	p_heads = head_table_empty();
	p_trans = fatrans_table_empty();
	p_index = fatrans_table_empty();
	p_trans.lastptr = &(p_trans.stack);
	p_trans.usestack = 0;
	p_index.usestack = 0;

	/* collect rules starting with the same heads */
	pds_prepare_check(mc_pds);

	/* build automaton for start configuration */
	state1 = mc_starthead->state;
	stack = mc_pds.start_stack;
	sprintf(tmpbuf,"__s%u__",(i=1));
	state2 = mc_sstate;

	Cudd_Ref(tmp0 = Cudd_bddAnd(mc_mgr,mc_pds.start_bdd,stack->bdd));
	Cudd_Ref(tmp1 = Cudd_bddPermute(mc_mgr,tmp0,mc_perm6));
	Cudd_RecursiveDeref(mc_mgr,tmp0);

	nt = fatrans_table_insert(&p_trans,
		fatrans_create(state1,stack->name,state2,0));
	add_bdd_trans(&p_trans,nt,tmp1,NULL,0);

	for (stack = stack->next; stack; stack = stack->next)
	{
		state1 = state2;
		sprintf(tmpbuf,"__s%u__",++i);
		state2 = name_create(tmpbuf);
		
		Cudd_Ref(tmp1 = Cudd_bddPermute(mc_mgr,stack->bdd,mc_perm6));
		nt = fatrans_table_insert(&p_trans,
				fatrans_create(state1,stack->name,state2,0));
		add_post_rel(&p_index,nt,tmp1,NULL);
	}

	demand_finished = 0;

	/* compute post* of start configuration */
	while ((t = p_trans.stack))
	{
		if (!(p_trans.stack = t->stack))
			p_trans.lastptr = &(p_trans.stack);
		t->stack = NULL;
		t->f &= ~FF_DUMB;

		if (!(t->f & FF_THEAD))
		{
			thead = fatrans_table_insert(&p_index,
				fatrans_create(t->from_state,t->name,0,0));
			t->list = thead->list;
			thead->list = t;
			t->f |= FF_THEAD;
		}

		Cudd_Ref(tmp0 = Cudd_bddOr(mc_mgr,t->rel,t->trans));
		Cudd_RecursiveDeref(mc_mgr,t->rel);
		t->rel = tmp0;
		tmp0 = t->trans;
		Cudd_Ref(t->trans = emptyset);
		edgecount++;

		if (mc_verbose > 2)
			printf("<< %s %s (%d)>>\n",name_cstring(t->from_state),
				name_cstring(t->name),mc_trace? t->origin->n:0);

		if (demand_finished && !t->b)
		{
			Cudd_RecursiveDeref(mc_mgr,tmp0);
			continue;
		}

		if ((head = head_find(mc_heads,t->from_state,t->name)))
		{
		    for (rule = head->fwd; rule; rule = rule->fwdnext)
			    /* <p,y> -> <p',y'y''> */
		    {
				if (!rule->tail) continue;

				if (mc_verbose > 2) printf(" ==> (%s, %s %s)\n",
					name_cstring(rule->headfwd->state),
					name_cstring(rule->headfwd->name),
					name_cstring(rule->tail));

				/* tmp1 = ex p',y': t->trans /\ rule->vars */
				Cudd_Ref(tmp1 = Cudd_bddAndAbstract(mc_mgr,tmp0,
				  rule->vars, (mc_restrict && rule->tail)? 
				 		 mc_cube9 : mc_cube3));
				if (tmp1 == emptyset) continue;

				if (!mc_restrict)
				{
						/* tmp2 = tmp1(y''->y') */
					Cudd_Ref(tmp2 = Cudd_bddPermute
						(mc_mgr,tmp1,mc_perm10));
					Cudd_RecursiveDeref(mc_mgr,tmp1);
				}
				else
					tmp2 = tmp1;

				/* tmp1 = (ex q,y',y''': tmp2)(p->p',y->y')
						/\ (p'=q) /\ (y'=y''') */
				Cudd_Ref(tmp1 = Cudd_bddExistAbstract
						(mc_mgr,tmp2,mc_cube7));
				Cudd_Ref(tmp3 = Cudd_bddPermute
						(mc_mgr,tmp1,mc_perm6));
				Cudd_RecursiveDeref(mc_mgr,tmp1);
				Cudd_Ref(tmp1 = Cudd_bddAnd
						(mc_mgr,tmp3,mc_qyeqv));
				Cudd_RecursiveDeref(mc_mgr,tmp3);

				/* (p,y,py,tmp1) */
				nt = fatrans_table_insert(&p_trans,
					fatrans_create(rule->headfwd->state,
						rule->headfwd->name,
						rule->origin->midstate,0));
				nt->prio = rule->origin->prio;
				add_bdd_trans(&p_trans,nt,tmp1,rule->origin,0);

		if (mc_reach) Cudd_Ref(tmp2);

				/* (py,y'',q,tmp2) */
				nt = fatrans_table_insert(&p_trans,
					fatrans_create(rule->origin->midstate,
					rule->tail,t->to_state,t->b | rule->b));
				add_post_rel(&p_index,nt,tmp2,rule->origin);
				/* t1 = (p'',eps,py) */

		if (mc_reach)
		{
		    if ((thead = fatrans_table_find(p_index,
				fatrans_create(0,0,rule->origin->midstate,0))))
			for (t1 = thead->list;t1; t1 = t1->list)
			{
			    OriginList newlist;

			    if (!mc_trace)
			    {
				/* tmp1 = ex p,y: tmp2 /\ t->rel */
				Cudd_Ref(tmp1 = Cudd_bddAndAbstract
						(mc_mgr,tmp2,t1->rel,mc_cube1));

				/* (p'',y'',q,tmp1) */
				nt = fatrans_table_insert(&p_trans,
					fatrans_create(t1->from_state,
					rule->tail,t->to_state,0));
				add_bdd_trans(&p_trans,nt,tmp1,NULL,0);
			    }
			    else for (newlist = t1->origin; newlist; 
						newlist = newlist->next)
			    {
				/* tmp1 = ex p,y: tmp2 /\ t->rel */
				Cudd_Ref(tmp1 = Cudd_bddAndAbstract
					(mc_mgr,tmp2,newlist->bdd,mc_cube1));

				if (tmp1 == emptyset) continue;

				/* (p'',y'',q,tmp1) */
				nt = fatrans_table_insert(&p_trans,
					fatrans_create(t1->from_state,
					rule->tail,t->to_state,0));
				add_bdd_trans(&p_trans,nt,tmp1,newlist->pt,
						rule->origin->midstate);
			    }
			}

		    Cudd_RecursiveDeref(mc_mgr,tmp2);
		}
		    }

		    for (rule = head->fwd; rule; rule = rule->fwdnext)
			    /* <p,y> -> <p',y'> */
		    {
			if (rule->tail) continue;

			if (mc_verbose > 2) printf(" ==> (%s, %s)\n",
				name_cstring(rule->headfwd->state),
				name_cstring(rule->headfwd->name));

			/* tmp1 = ex p',y': t->trans /\ rule->vars */
			Cudd_Ref(tmp1 = Cudd_bddAndAbstract(mc_mgr,tmp0,
					rule->vars,(mc_restrict && rule->tail)?
						mc_cube9 : mc_cube3));
//if (tmp0 == emptyset) printf("tmp0 is empty\n");
//if (rule->vars == emptyset) printf("vars are empty\n");
//if (tmp1 == emptyset) printf("tmp1 is empty\n");
			if (tmp1 == emptyset) continue;

			/* pt->to_stack1 != 0 /\ pt->to_stack2 = 0 */

			/* tmp2 = tmp1(p->p',y->y') */			
			Cudd_Ref(tmp2 = Cudd_bddPermute(mc_mgr,tmp1,mc_perm6));
			Cudd_RecursiveDeref(mc_mgr,tmp1);

			nt = fatrans_table_insert(&p_trans,
					fatrans_create(rule->headfwd->state,
						rule->headfwd->name,
						t->to_state,t->b | rule->b));
			nt->prio = rule->origin->prio;
			add_bdd_trans(&p_trans,nt,tmp2,
					rule->origin,rule->midstate);
//printf("tmp2 is %sempty\n",tmp2==emptyset? "" : "non");
		    }
		}

		if ((head = head_find(p_heads,t->from_state,t->name)))
		    for (pt = head->post; pt; pt = pt->post)
				/* <p,y> -> <p',e> */
		    {
			/* pt->to_stack1 == 0 */
			if (mc_verbose > 2) pds_print_trans(pt);

			/* tmp1 = ex p',y': t->trans /\ rule->vars */
			Cudd_Ref(tmp1 = Cudd_bddAndAbstract(mc_mgr,
				tmp0,pt->vars,mc_cube3));
			if (tmp1 == emptyset) continue;

			/* tmp2 = tmp1(p->p',q->p,y'''->y) */
			Cudd_Ref(tmp2 = Cudd_bddPermute(mc_mgr,tmp1,mc_perm11));
			Cudd_RecursiveDeref(mc_mgr,tmp1);

			/* (p,e,q) */
			nt = fatrans_table_insert(&p_index, fatrans_create(
				pt->to_state,0,t->to_state, t->b | pt->b));
			Cudd_Ref(tmp3 =
				Cudd_bddAnd(mc_mgr,tmp2,Cudd_Not(nt->rel)));

			if (tmp3 == emptyset)
			{
				Cudd_RecursiveDeref(mc_mgr,tmp2);
				continue;
			}

			add_eps_rel(&p_index,nt,tmp2,pt);

			/* for t1 = (q,y'',q') */
			if ((thead = fatrans_table_find(p_index,
					fatrans_create(t->to_state,0,0,0))))
			    for (t1 = thead->list; t1; t1 = t1->list)
			    {
				nt = fatrans_table_insert(&p_trans,
					fatrans_create(pt->to_state,t1->name,
					t1->to_state, t->b | pt->b | t1->b));

				/* tmp1 = ex p,y: tmp3 /\ t1->rel */
				Cudd_Ref(tmp1 = Cudd_bddAndAbstract(
						mc_mgr,tmp3,t1->rel,mc_cube1));
				add_bdd_trans(&p_trans,nt,tmp1,pt,t->to_state);
			    }

		if (!mc_reach)
		{
		    /* tmp2 = tmp3(p'->q) */
		    Cudd_Ref(tmp2 = Cudd_bddPermute(mc_mgr,tmp3,mc_perm4));
		    Cudd_RecursiveDeref(mc_mgr,tmp3);

		    /* create new rules: for all <p,y> -> <p',y'y''> */
		    if ((head1 = get_head_from_state(t->to_state)))
			for (rule = head1->rules; rule; rule = rule->next)
			{
			    if (!rule->tail) continue;

			    /*tmp3 = (ex p,y: tmp2 /\ rule->vars)(q->p,y''->y)*/
			    Cudd_Ref(tmp1 = Cudd_bddAndAbstract(mc_mgr,
						tmp2,rule->vars,mc_cube1));
			    Cudd_Ref(tmp3 =
				    Cudd_bddPermute(mc_mgr,tmp1,mc_perm2));
			    Cudd_RecursiveDeref(mc_mgr,tmp1);

			    /* add <p,y> -> <p'',y''> with tmp3 */
			    newhead = head_table_insert(&mc_heads,
					head_create(pt->to_state, rule->tail));

			    if (mc_verbose > 2)
				printf("adding rule <%s %s> -> <%s %s>\n",
						name_cstring(rule->head->state),
						name_cstring(rule->head->name),
						name_cstring(newhead->state),
						name_cstring(newhead->name));

			    head_add_rule(newhead, rule->head, 0,
					t->b | rule->b | pt->b, 1,
					pt, rule->origin->midstate, tmp3);

			    Cudd_RecursiveDeref(mc_mgr,tmp3);
			}

		    Cudd_RecursiveDeref(mc_mgr,tmp2);
		}
		else  /* just add the rule with false for the dfs to succeed */
		{
			Cudd_RecursiveDeref(mc_mgr,tmp3);

			/* create new rules: for all <p,y> -> <p',y'y''> */
			if ((head1 = get_head_from_state(t->to_state)))
			  for (rule = head1->rules; rule; rule = rule->next)
			  {
				if (!rule->tail) continue;

				/* add <p,y> -> <p'',y''> with false */
				newhead = head_table_insert(&mc_heads,
					head_create(pt->to_state, rule->tail));

				if (mc_verbose > 2)
				    printf("adding rule <%s %s> -> <%s %s>\n",
						name_cstring(rule->head->state),
						name_cstring(rule->head->name),
						name_cstring(newhead->state),
						name_cstring(newhead->name));

				head_add_rule(newhead, rule->head, 0,
					t->b | rule->b | pt->b, 1,
					pt, rule->origin->midstate, emptyset);
			  }

		}
			}

		Cudd_RecursiveDeref(mc_mgr,tmp0);
		if (mc_verbose > 2) printf("===\n");
	}

	common_resource_displaymark(2, "post*", &mctime_post);
	if (mc_verbose) printf("%d edges in the automaton\n",edgecount);

	get_rid_of_the_bs(&p_trans);

	dfs_search(mc_starthead);

	common_resource_setmark(2);

	/* restrict rules to reachable states */
	for (head = dfs_found; head; head = head->stack)
	{
		if (mc_verbose > 1) printf("<%s %s>\n",
			name_cstring(head->state),name_cstring(head->name));
		Cudd_Ref(tmp0 = emptyset);
		thead = fatrans_table_find(p_index,
			    fatrans_create(head->state,head->name,0,0));
		if (thead)
		{
		    for (t1 = thead->list; t1; t1 = t1->list)
		    {
			/* tmp0 = tmp0 \/ ex q,y''': t1->rel */
			Cudd_Ref(tmp1
			    = Cudd_bddExistAbstract(mc_mgr,t1->rel,mc_cube8));
			Cudd_Ref(tmp2 = Cudd_bddOr(mc_mgr,tmp0,tmp1));
			Cudd_RecursiveDeref(mc_mgr,tmp0);
			Cudd_RecursiveDeref(mc_mgr,tmp1);
			tmp0 = tmp2;
		    }
		}
		
		for (rule = head->fwd; rule; rule = rule->fwdnext)
		{
		    Cudd_Ref(tmp1 = Cudd_bddAnd(mc_mgr,rule->vars,tmp0));
		    Cudd_RecursiveDeref(mc_mgr,rule->vars);
		    rule->vars = tmp1;
		}

		Cudd_RecursiveDeref(mc_mgr,tmp0);
	}

	common_resource_displaymark(2, "pruning", NULL);

	head = find_cycles();

	if (mc_bp && mc_reach && mc_trace > 1)
	{
		printf("%s; Label %s %sreachable.\n",
			head? "YES" : "NO", name_cstring(bp_reach_target_label),
			head? "" : "un");
	}
	else
		printf((!!head ^ !!mc_reach)? "NO.\n" : "YES.\n");

	if (mc_reach > 1) print_post_automaton(&p_trans);
	if (mc_stop_after_post) return;
	if (head && mc_trace) get_post_trace(head);

	return;
}
