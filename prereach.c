/* =========================================================================

   Reachability algorithm
   full-addition version
   with demand option

   ====================================================================== */

#include <stdio.h>
#include "mcheck.h"
#include "cycle.h"
#include "common.h"
#include "variables.h"

extern Name reach_target_state;
extern Name reach_target_stack;

/* For reachability, compute all configurations backwards reachable
 * from the target. */

void compute_prestar_reachability ()
{
	DdNode		*tmp0, *tmp1, *tmp2, *tmp3;
	FATransition	nt, t, t1, thead;
	Head		head, newhead;
	Rule		rule;

	common_resource_setmark(2);

	mc_heads = head_table_empty();
	mc_trans = fatrans_table_empty();
	mc_index = fatrans_table_empty();
	mc_trans.lastptr = &(mc_trans.stack);
	mc_trans.usestack = 0;
	mc_index.usestack = FAT_LIST_MARK;
	mc_trans.list = LIST_END;

	pds_prepare_check(mc_pds);

	nt = fatrans_table_insert(&mc_trans,
	     fatrans_create(reach_target_state,reach_target_stack,mc_sstate,0));
	Cudd_Ref(fullset);
	add_bdd_trans(&mc_trans,nt,fullset,NULL,0);

	common_resource_displaymark(2, "building pds",NULL);
	common_resource_setmark(2);

	/* compute epsilon transitions with bdds */

	common_resource_displaymark(2, "pre* first pass",NULL);
	common_resource_setmark(2);

	demand_finished = 0;
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

	    if (!(t->f & FF_THEAD))
	    {
		    thead = fatrans_table_insert(&mc_index,
			fatrans_create(t->from_state,t->name,0,0));
		    t->list = thead->list;
		    thead->list = t;
		    t->f |= FF_THEAD;
	    }

	    Cudd_Ref(tmp0 = Cudd_bddOr(mc_mgr,t->trans,t->rel));
	    Cudd_RecursiveDeref(mc_mgr,t->rel);
	    t->rel = tmp0;
	    tmp1 = t->trans;
	    Cudd_Ref(t->trans = emptyset);

	    if (demand_finished && !t->b)
	    {
		Cudd_RecursiveDeref(mc_mgr,tmp1);
		continue;
	    }

	    if ((head = head_find(mc_heads,t->from_state,0)))
	    {
		for (rule = head->rules; rule; rule = rule->next)
		{
		    /* tmp3 = rule->vars(p'->p,y'->y,p->q) */
		    Cudd_Ref(tmp3=Cudd_bddPermute(mc_mgr,rule->vars,mc_perm5));
		    nt = fatrans_table_insert(&mc_trans,fatrans_create
			  (rule->head->state,rule->head->name,t->from_state,0));
		    add_bdd_trans(&mc_trans,nt,tmp3,rule->origin,0);
		}
		head->rules = NULL;
	    }

	    if ((head = head_find(mc_heads,t->from_state,t->name)))
		for (rule = head->rules; rule; rule = rule->next)
		{
		    /* tmp0 = ex p,y: (t->trans /\ rule->vars) */
		    Cudd_Ref(tmp0 =
			Cudd_bddAndAbstract(mc_mgr,tmp1,rule->vars,mc_cube1));
		    
		    if (rule->tail)
		    {
			/* tmp2 = tmp0(q->p,y''->y) */
			Cudd_Ref(tmp2 = Cudd_bddPermute(mc_mgr,tmp0,mc_perm2));
			Cudd_RecursiveDeref(mc_mgr,tmp0);
			newhead = head_table_insert(&mc_heads,
					head_create(t->to_state, rule->tail));
			head_add_rule(newhead, rule->head, 0, 0, 1,
				rule->origin, 0, tmp2);

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

				nt = fatrans_table_insert(&mc_trans,
				    fatrans_create(rule->head->state,
					rule->head->name, t1->to_state,0));
				add_bdd_trans(&mc_trans,nt,
						tmp0,rule->origin, t->to_state);
			    }

			if (t->to_state == mc_sstate)
			{
				/* tmp3 = ex p,y: (tmp2 /\ true) */
				Cudd_Ref(tmp3 = Cudd_bddAndAbstract
					(mc_mgr,tmp2,fullset,mc_cube1));
				/* tmp0 = tmp3(p'->p,y'->y) */
				Cudd_Ref(tmp0 =
				   Cudd_bddPermute(mc_mgr,tmp3,mc_perm1));
				Cudd_RecursiveDeref(mc_mgr,tmp3);

				nt = fatrans_table_insert(&mc_trans,
				    fatrans_create(rule->head->state,
					rule->head->name, mc_sstate,0));
				add_bdd_trans(&mc_trans,nt,
						tmp0,rule->origin,mc_sstate);
			}

			Cudd_RecursiveDeref(mc_mgr,tmp2);
		    }
		    else
		    {
			/* tmp2 = tmp0(p'->p,y'->y) */
			Cudd_Ref(tmp2 = Cudd_bddPermute(mc_mgr,tmp0,mc_perm1));
			Cudd_RecursiveDeref(mc_mgr,tmp0);
			nt = fatrans_table_insert(&mc_trans,
			    fatrans_create(rule->head->state, rule->head->name,
				t->to_state, rule->b));
			add_bdd_trans(&mc_trans,nt,tmp2,rule->origin,
					rule->new? t->from_state : 0);
		    }
		}

	    Cudd_RecursiveDeref(mc_mgr,tmp1);
	}

	common_resource_displaymark(2, "pre* second pass",&mctime_pre2);

	/* evaluate the result */
	get_pre_trace();
}
