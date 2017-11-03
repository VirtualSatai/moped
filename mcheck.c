/* =========================================================================

   Model-Checking algorithm

   ====================================================================== */

#include <stdio.h>
#include "mcheck.h"
#include "common.h"
#include "variables.h"
#include "ba.h"

int mc_age = 0;
char demand_finished;

void add_bdd_trans (FATransTable *table, FATransition t,
			DdNode *newbdd, PDSTransition origin, Name midstate)
{
	DdNode *tmp0, *tmp1, *tmp2;

	Cudd_Ref(tmp0 = Cudd_bddAnd(mc_mgr,newbdd,Cudd_Not(t->rel)));
	Cudd_RecursiveDeref(mc_mgr,newbdd);

	if (mc_trace)
	{
		OriginList newlist;

		Cudd_Ref(tmp2 = Cudd_bddAnd(mc_mgr,tmp0,Cudd_Not(t->trans)));
		if (tmp2 != emptyset)
		{
		    newlist = common_malloc(sizeof(struct OriginListElement));
		    newlist->pt = origin;
		    newlist->midstate = midstate;
		    newlist->bdd = tmp2;
		    newlist->n = ++mc_age;
		    if (mc_verbose > 2)
			{
			    printf("\t==> %d (%p,%d)\n",mc_age,t,t->b);
			    printf("\trel = ");
			    print_bdd(t->rel,rule_set,0,0,0,0);
			    printf("\ttmp2 = ");
			    print_bdd(tmp2,rule_set,0,0,0,0);
			}
		    newlist->next = t->origin;
		    t->origin = newlist;
		}
	}

	Cudd_Ref(tmp1 = Cudd_bddOr(mc_mgr,t->trans,tmp0));
	Cudd_RecursiveDeref(mc_mgr,t->trans);
	Cudd_RecursiveDeref(mc_mgr,tmp0);
	t->trans = tmp1;

	if ((t->f & FF_DUMB) || t->trans == emptyset) return;

	if (mc_reach && mc_demand && t->b)
		demand_finished = 1;

	if (mc_queue == 0)	// DFS
	{
		t->stack = table->stack;
		table->stack = t;
	}
	else if (mc_queue == 1)	// BFS
	{
		*(table->lastptr) = t;
		table->lastptr = &(t->stack);
	}
	else if (mc_queue == 2)	// prio
	{
		// fixme: should really do this with a proper prio queue
		FATransition st, *lst;
		for (st = table->stack, lst = &(table->stack); st; 
				lst = &(st->stack), st = st->stack)
			if (st->prio >= t->prio) break;

		t->stack = st;
		*lst = t;
	}
	t->f |= FF_DUMB;
}

void add_bdd_head (Head *vstk, Head hd, DdNode *newbdd)
{
	DdNode *tmp0;

	if (newbdd == emptyset) return;
	if (hd->trans != emptyset)
	{
		Cudd_Ref(tmp0 = Cudd_bddOr(mc_mgr,hd->trans,newbdd));
		Cudd_RecursiveDeref(mc_mgr,newbdd);
		Cudd_RecursiveDeref(mc_mgr,hd->trans);
	}
	else
		tmp0 = newbdd;

	hd->trans = tmp0;

	if (hd->vstack || hd->trans == emptyset) return;
	hd->vstack = *vstk;
	*vstk = hd;
}

void merge_origins (OriginList o1, OriginList o2, OriginList *o3, DdNode **set)
{
	DdNode *tmp0;

	if (!o1 && !o2) return;

	if (o1 && o2)
	{
		if (o1->n > o2->n) merge_origins(o1->next,o2,o3,set);
			else	   merge_origins(o1,o2->next,o3,set), o1 = o2;
	}
	else
	{
		if (!o1) o1 = o2;
		merge_origins(o1->next,NULL,o3,set);
	}

	Cudd_Ref(tmp0 = Cudd_bddAnd(mc_mgr,o1->bdd,Cudd_Not(*set)));
	Cudd_RecursiveDeref(mc_mgr,o1->bdd);
	if (tmp0 == emptyset)
	{
		common_free(o1,sizeof(struct OriginListElement));
		return;
	}

	o1->bdd = tmp0;
	Cudd_Ref(tmp0 = Cudd_bddOr(mc_mgr,*set,o1->bdd));
	Cudd_RecursiveDeref(mc_mgr,*set);
	*set = tmp0;

	o1->next = *o3;
	*o3 = o1;
}

void delete_from_list (FATransTable table, Name state, Name stack,
			FATransition t1)
{
	FATransition *t, thead = fatrans_table_find(table,
					fatrans_create(state,stack,0,0));

	if (!thead) return;
	for (t = &(thead->list); *t; t = &((*t)->list))
		if (*t == t1) { *t = t1->list; return; }
}

void get_rid_of_the_bs (FATransTable *table)
{
	FATransition t, t1;
	OriginList o3;
	DdNode *tmp0;
	int i;

	for (i = 0; i < table->size; i++)
	    for (t = table->data[i]; t; t = t->next)
	    {
		if (!t->next) continue;
		if (fatrans_compare_simple(t,t->next)) continue;

		t->b = 0;

		Cudd_Ref(tmp0 = Cudd_bddOr(mc_mgr,t->rel,t->next->rel));
		Cudd_RecursiveDeref(mc_mgr,t->rel);
		Cudd_RecursiveDeref(mc_mgr,t->next->rel);
		t->rel = tmp0;

		o3 = NULL; Cudd_Ref(tmp0 = emptyset);
		merge_origins(t->origin,t->next->origin,&o3,&tmp0);
		t->origin = o3;
		Cudd_RecursiveDeref(mc_mgr,tmp0);

		t1 = t->next;
		t->next = t1->next;

		if (mc_poststar)
		{
			delete_from_list(p_index,t->from_state,t->name,t1);
			delete_from_list(p_index,t->from_state,0,t1);
		}
		else
			delete_from_list(mc_index,t->from_state,t->name,t1);

		fatrans_delete(t1);
	    }
}


void get_names_from_state (Name state, Name *ctrl, Name *stack)
{
	char *ts, *tt;

	/* extract p,y from the state name */
	ts = strdup(name_cstring(state));
	tt = strchr(ts,'~');
	if (!tt)
	{
		free(ts);
		*ctrl = *stack = -1;
		return;
	}

	*tt = 0;
	*strchr(tt+1,'^') = 0;
	*ctrl = name_create(ts+1);
	*stack = name_create(tt+1);
	free(ts);
}

Head get_head_from_state (Name state)
{
	Name state1, state2;

	get_names_from_state(state,&state1,&state2);
	if (state1 < 0) return NULL;
	return head_find(mc_heads,state1,state2);
}


/* Compute the backwards reachable states from goal back to goal
   within the component given by cstart. Consider only pathes that
   start with a c-labelled edge. */

DdNode *compute_rep (Head goal, Head cstart, char c)
{
	DdNode *tmp0 = NULL, *tmp1, *tmp2;
	Head head, newhead;
	Rule rule;

	Head dummyhd = head_create(0,0);
	Head vstk = dummyhd;

	if (mc_verbose) common_resource_setmark(3);

	for (rule = goal->rules; rule; rule = rule->next)
	{
		if (rule->b != c) continue;
		head = rule->head;
 		if (head->comp != goal->comp) continue;

		/* tmp0 = rule->vars(q->p,y''->y) */
		Cudd_Ref(tmp0 = Cudd_bddPermute(mc_mgr,rule->vars,mc_perm2));
		add_bdd_head(&vstk,head,tmp0);
	}

	while (vstk != dummyhd)
	{
		head = vstk;
		vstk = head->vstack;
		head->vstack = NULL;

		if (head != goal) Cudd_Ref(tmp0 =
			Cudd_bddAnd(mc_mgr,head->trans,Cudd_Not(head->rel)));
		Cudd_Ref(tmp1 = Cudd_bddOr(mc_mgr,head->trans,head->rel));
		Cudd_RecursiveDeref(mc_mgr,head->rel);
		Cudd_RecursiveDeref(mc_mgr,head->trans);
		head->rel = tmp1;
		Cudd_Ref(head->trans = emptyset);
		if (head == goal) continue;

		/* tmp1 = tmp0(p'->q,y'->y'') */
		Cudd_Ref(tmp1 = Cudd_bddVarMap(mc_mgr,tmp0));
		Cudd_RecursiveDeref(mc_mgr,tmp0);

		for (rule = head->rules; rule; rule = rule->next)
		{
		   newhead = rule->head;
		   if (newhead->comp != goal->comp) continue;

		   /* tmp2 = ex q,y'': rule.vars /\ tmp1 */
		   Cudd_Ref(tmp2 =
			Cudd_bddAndAbstract(mc_mgr,rule->vars,tmp1,mc_cube2));
		   add_bdd_head(&vstk,newhead,tmp2);
		}

		Cudd_RecursiveDeref(mc_mgr,tmp1);
	}

	Cudd_Ref(tmp0 = goal->rel);
	for (head = cstart; head && head->comp == goal->comp;
			head = head->stack)
	if (head->rel != emptyset)
	{
		Cudd_RecursiveDeref(mc_mgr,head->rel);
		Cudd_Ref(head->rel = emptyset);
	}

	if (mc_verbose) common_resource_displaymark(3,"summary",NULL);
	free(dummyhd);
	return tmp0;
}
