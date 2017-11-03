/* =========================================================================

   Model-Checking algorithm

   ====================================================================== */

#include <stdio.h>
#include "mcheck.h"
#include "cycle.h"
#include "common.h"
#include "variables.h"

extern void compute_prestar_reachability ();

/* The main function. Compute an automaton for all configurations that
   have accepting runs using the pre* method. */

void compute_prestar ()
{
	DdNode		*tmp0, *tmp1, *tmp2, *tmp3;
	FATransition	nt, t, t1, thead;
	Head		head, newhead;
	Rule		rule;

	if (mc_reach) { compute_prestar_reachability(); return; }

	common_resource_setmark(2);

	mc_heads = head_table_empty();
	mc_trans = fatrans_table_empty();
	mc_index = fatrans_table_empty();
	mc_trans.lastptr = &(mc_trans.stack);
	mc_trans.usestack = 0;
	mc_index.usestack = FAT_LIST_MARK;
	mc_trans.list = LIST_END;

	pds_prepare_check(mc_pds);

	common_resource_displaymark(2, "building pds",NULL);
	common_resource_setmark(2);

	/* compute epsilon transitions without bdds */

	mc_trans.usestack = FAT_USE_LIST;
	/* take next transition t = (p,[y,b],p') */
	while ((t = mc_trans.list) != LIST_END)
	{
	    mc_trans.list = t->list;

	    /* add t to transitions starting with (p,y) */
	    thead = fatrans_table_insert(&mc_index,
			fatrans_create(t->from_state,t->name,0,0));
	    t->list = thead->list;
	    thead->list = t;

	    if ((head = head_find(mc_heads,t->from_state,t->name)))
		for (rule = head->rules; rule; rule = rule->next)
		{
		    if (rule->tail)
		    {
			/* for every rule (p2,y2) -> (p,yy1) */
			/* add (p2,y2) -> (p',y1) to Delta' */

			newhead = head_table_insert(&mc_heads,
					head_create(t->to_state, rule->tail));
			head_add_rule(newhead, rule->head, 0, t->b | rule->b, 1,
					rule->origin, 0, emptyset);

			/* for every (b',q'') s.t. t1=(p',[y1,b'],p'') in rel */
			if ((thead = fatrans_table_find(mc_index,
			  fatrans_create(t->to_state,rule->tail,0,0))))
			    for (t1 = thead->list; t1!=LIST_END; t1 = t1->list)
			    {
				/* add (p2,[y2,b v b' v G(p2)],p'') */

				nt = fatrans_table_insert(&mc_trans,
				    fatrans_create(rule->head->state,
					rule->head->name, t1->to_state,
					t->b | t1->b | rule->b));
			    }
		    }
		    else
		    {
			/* for every rule (p1,y1) -> (p,y) */
			/* add (p1,[y1,b v G(q1)],p') */

			/* tmp2 = tmp0(p'->p,y'->y) */
			nt = fatrans_table_insert(&mc_trans,
			    fatrans_create(rule->head->state, rule->head->name,
				t->to_state, t->b | rule->b));
		    }
		}
	}

	/* identify reachable heads and components */

	dfs_search(mc_starthead);

	/* compute epsilon transitions with bdds */

	common_resource_displaymark(2, "pre* first pass",NULL);
	common_resource_setmark(2);

	mc_trans.usestack = 0;
	while ((t = mc_trans.stack))
	{
	    if (!(mc_trans.stack = t->stack))
			mc_trans.lastptr = &(mc_trans.stack);
	    t->stack = NULL;
		t->f &= ~FF_DUMB;

	    if (mc_verbose > 2) printf("%s %s %s\n",
			name_cstring(t->from_state), name_cstring(t->name),
			name_cstring(t->to_state));

	    thead = fatrans_table_find(mc_index,
			fatrans_create(t->from_state,t->name,0,0));

	    Cudd_Ref(tmp0 = Cudd_bddOr(mc_mgr,t->trans,t->rel));
	    Cudd_RecursiveDeref(mc_mgr,t->rel);
	    t->rel = tmp0;
	    tmp1 = t->trans;
	    Cudd_Ref(t->trans = emptyset);

	    if ((head = head_find(mc_heads,t->from_state,t->name)))
		for (rule = head->rules; rule; rule = rule->next)
		{
		    /* ignore if not reachable in control flow */
		    if (!rule->head->comp) continue;

		    /* tmp0 = ex p,y: (t->trans /\ rule->vars) */
		    Cudd_Ref(tmp0 =
			Cudd_bddAndAbstract(mc_mgr,tmp1,rule->vars,mc_cube1));
		    
		    if (rule->tail)
		    {
			/* tmp2 = tmp0(q->p,y''->y) */
			Cudd_Ref(tmp2 = Cudd_bddPermute(mc_mgr,tmp0,mc_perm2));
			Cudd_RecursiveDeref(mc_mgr,tmp0);
			newhead = head_find(mc_heads, t->to_state, rule->tail);
			head_add_rule(newhead, rule->head, 0,
				t->b | rule->b, 1, rule->origin, 0, tmp2);

			if ((thead = fatrans_table_find(mc_index,
			  fatrans_create(t->to_state,rule->tail,0,0))))
			    for (t1 = thead->list; t1!=LIST_END; t1 = t1->list)
			    {
				/* tmp3 = ex p,y: (tmp2 /\ t1->rel) */
				Cudd_Ref(tmp3 = Cudd_bddAndAbstract
					(mc_mgr,tmp2,t1->rel,mc_cube1));
				/* tmp0 = tmp3(p'->p,y'->y) */
				Cudd_Ref(tmp0 =
				   Cudd_bddPermute(mc_mgr,tmp3,mc_perm1));
				Cudd_RecursiveDeref(mc_mgr,tmp3);

				nt = fatrans_table_find(mc_trans,
				    fatrans_create(rule->head->state,
					rule->head->name, t1->to_state,
					t->b | t1->b | rule->b));
				add_bdd_trans(&mc_trans,nt,
						tmp0,rule->origin, t->to_state);
			    }
			Cudd_RecursiveDeref(mc_mgr,tmp2);
		    }
		    else
		    {
			/* tmp2 = tmp0(p'->p,y'->y) */
			Cudd_Ref(tmp2 = Cudd_bddPermute(mc_mgr,tmp0,mc_perm1));
			Cudd_RecursiveDeref(mc_mgr,tmp0);
			nt = fatrans_table_find(mc_trans,
			    fatrans_create(rule->head->state, rule->head->name,
				t->to_state, t->b | rule->b));
			add_bdd_trans(&mc_trans,nt,tmp2,rule->origin,
					rule->new? t->from_state : 0);
		    }
		}

	    Cudd_RecursiveDeref(mc_mgr,tmp1);
	}

	common_resource_displaymark(2, "pre* second pass",&mctime_pre2);

	/* unite 0 and 1 transitions */
	get_rid_of_the_bs(&mc_trans);

	/* search for accepting cycles */
	find_cycles();

	/* simplified prestar algorithm for additional arcs */

	common_resource_setmark(2);

	while ((t = mc_trans.stack))	/* t->to_state == mc_sstate */
	{
	    /* advance stack */
	    if (!(mc_trans.stack = t->stack))
			mc_trans.lastptr = &(mc_trans.stack);
	    t->stack = NULL;
		t->f &= ~FF_DUMB;

	    /* add t to transitions starting with (p,y) */
	    thead = fatrans_table_insert(&mc_index,
			fatrans_create(t->from_state,t->name,0,0));
	    if (!t->list) { t->list = thead->list; thead->list = t; }
		

	    Cudd_Ref(tmp0 = Cudd_bddOr(mc_mgr,t->trans,t->rel));
	    Cudd_RecursiveDeref(mc_mgr,t->rel);
	    t->rel = tmp0;
	    tmp1 = t->trans;
	    Cudd_Ref(t->trans = emptyset);

	    if (mc_verbose > 1) printf("%s %s\n",
			name_cstring(t->from_state),name_cstring(t->name));

	    if ((head = head_find(mc_heads,t->from_state,t->name)))
		for (rule = head->rules; rule; rule = rule->next)
		{
		    /* ignore if not reachable */
		    if (!rule->head->comp) continue;

		    /* for every rule (p1,y1) -> (p,yy2) */
		    /* for every rule (p1,y1) -> (p,y) */
		    /* add (p1,y1,s) */

		    /* tmp0 = ex p,y: tmp1 /\ rule->vars */
		    Cudd_Ref(tmp0 =
			Cudd_bddAndAbstract(mc_mgr,tmp1,rule->vars,mc_cube1));
		    /* tmp3 = tmp0(p'->p,y'->y) */
		    Cudd_Ref(tmp3 = Cudd_bddPermute(mc_mgr,tmp0,mc_perm1));
		    Cudd_RecursiveDeref(mc_mgr,tmp0);

		    nt = fatrans_table_insert(&mc_trans,
			fatrans_create(rule->head->state, rule->head->name,
			    mc_sstate, 0));
		    add_bdd_trans(&mc_trans,nt,tmp3,rule->origin,
			rule->tail? mc_sstate : rule->new? t->from_state : 0);
		}

	    Cudd_RecursiveDeref(mc_mgr,tmp1);
	}

	common_resource_displaymark(2, "pre*",&mctime_pre3);

	/* evaluate the result */
	get_pre_trace();
}
