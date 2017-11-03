/* =========================================================================

   Definition der Datenstrukturen und Funktionen
   zur Verwaltung von Pushdown Systemen

   ====================================================================== */

#include <stdio.h>
#include <string.h>

#include "ba.h"
#include "pds.h"
#include "common.h"
#include "mcheck.h"
#include "bpstruc.h"
#include "expr.h"

extern BuechiAutomaton	mc_ba;
extern int mc_reach;
extern Name bp_qstate;
extern bp_fun_t bp_functions;

void add_bdd_trans (FATransTable*,FATransition,DdNode*,PDSTransition,Name);

PushdownSystem pds_empty()
{
	PushdownSystem pds;

	pds.start_state = 0;
	pds.start_stack = NULL;
	pds.start_bdd = NULL;
	pds.transitions = NULL;
	pds.lasttrans = NULL;
	return pds;
}

void pds_delete (PushdownSystem *pds)
{
	NameStack t;

	for (t = pds->start_stack; t; t = t->next)
		Cudd_RecursiveDeref(mc_mgr,t->bdd);

	name_stack_delete(&(pds->start_stack));
	pdstrans_list_delete(&(pds->transitions));
}

void pds_insert_trans (PushdownSystem *pds, Name from_state, Name from_stack,
	Name to_state, Name to_stack1, Name to_stack2, DdNode *vars, char *lab,
	int prio)
{
	BATransition t;
	DdNode *tmp0, *tmp1;
	int bf, bt, l1, l2;
	char *b1, *b2, *c1, *c2, *c3, *c4;

	if (mc_reach)
	{
		pdstrans_list_insert(pds,
			pdstrans_create(from_state, from_stack,
			    to_state, to_stack1, to_stack2, lab, prio), vars);
		return;
	}

	for (t = mc_ba.transitions; t; t = t->next)
	{
		tmp0 = build_condition(t->condition,from_state,from_stack);
		Cudd_Ref(tmp1 = Cudd_bddAnd(mc_mgr,vars,tmp0));
		Cudd_RecursiveDeref(mc_mgr,tmp0);
		if (tmp1 == emptyset) continue;

		bf = ba_is_finalstate(t->from_state);
		bt = ba_is_finalstate(t->to_state);

		c1 = name_cstring(t->from_state);
		c2 = name_cstring(from_state);
		c3 = name_cstring(t->to_state);
		c4 = name_cstring(to_state);

		b1 = common_malloc(l1 = strlen(c1) + strlen(c2) + 3);
		sprintf(b1,"%c%s.%s", bf? '$' : 'p', c2, c1);
		b2 = common_malloc(l2 = strlen(c3) + strlen(c4) + 3);
		sprintf(b2,"%c%s.%s", bt? '$' : 'p', c4, c3);

		pdstrans_list_insert(pds,
			pdstrans_create(name_create(b1), from_stack,
			    name_create(b2), to_stack1, to_stack2, lab, prio),
			tmp1);

		common_free(b1,l1); common_free(b2,l2);
	}
}

PDSTransition pdstrans_create (Name from_state, Name from_stack, Name to_state,
				Name to_stack1, Name to_stack2, char *label,
				int prio)
{
	PDSTransition new_transition;

	new_transition = common_malloc(sizeof(struct PDSTransitionStruct));

	new_transition->from_state = from_state;
	new_transition->from_stack = from_stack;
	new_transition->to_state   = to_state;
	new_transition->to_stack1  = to_stack1;
	new_transition->to_stack2  = to_stack2;
	new_transition->label	   = label? strdup(label) : NULL;
	new_transition->post	   = NULL;
	new_transition->b          = pds_is_finalstate(from_state);
	new_transition->prio   = prio;
   
	return new_transition;
}

void pdstrans_delete (PDSTransition transition)
{
	common_free(transition,sizeof(struct PDSTransitionStruct));
}

void pdstrans_list_delete (PDSTransList *trans_list)
{
	while (*trans_list)
	{
		PDSTransition entry = *trans_list;
		*trans_list = (*trans_list)->next;
		pdstrans_delete(entry);
	}
}

void pdstrans_list_insert(PushdownSystem *pds, PDSTransition pt,
				DdNode *vars)
{
	Cudd_Ref(pt->vars = vars);

	if (mc_verbose > 2) pds_print_trans(pt);

	/* insert at end */
	if (!pds->transitions)
		pds->transitions = pds->lasttrans = pt;
	else
	{
		pds->lasttrans->next = pt;
		pds->lasttrans = pt;
	}
	pt->next = NULL;

	/* insert at front */
	/* pt->next = pds->transitions;
	   pds->transitions = pt; */
}

void pds_find_starthead (PushdownSystem pds)
{
	int bf = ba_is_finalstate(mc_ba.start_state);
	char* c1 = name_cstring(pds.start_state);
	char* c2 = name_cstring(mc_ba.start_state);
	char *b = common_malloc(strlen(c1) + strlen(c2) + 3);

	sprintf(b, "%c%s.%s", bf? '$' : 'p', c1, c2);
	
	mc_starthead = head_table_insert(&mc_heads,
			head_create(mc_reach? pds.start_state : name_create(b),
			pds.start_stack->name));
	free(b);
}

void pds_prepare_check (PushdownSystem pds)
{
	PDSTransList pt;
	Head head1, head2;
	FATransition nt;
	DdNode *tmp;

	for (pt = pds.transitions; pt; pt = pt->next)
	{
		if (!pt->to_stack1)
		{
		    if (mc_poststar)
		    {
			head1 = head_table_insert(&p_heads,
				head_create(pt->from_state,pt->from_stack));
			pt->post = head1->post;
			head1->post = pt;
			continue;
		    }
		    else if (!mc_reach)
		    {
			nt = fatrans_table_insert(&mc_trans,
				fatrans_create(pt->from_state, pt->from_stack,
				pt->to_state, pt->b));
			Cudd_Ref(tmp
				= Cudd_bddPermute(mc_mgr,pt->vars,mc_perm5));
			add_bdd_trans(&mc_trans,nt,tmp,pt,0);
			if (nt->list) continue;
			nt->list = mc_trans.list;
			mc_trans.list = nt;
			continue;
		    }
		}

		if (pt->to_stack2 && mc_poststar)
		{
			char* c1 = name_cstring(pt->to_state);
			char* c2 = name_cstring(pt->to_stack1);
			char *b = common_malloc(strlen(c1) + strlen(c2) + 4);

			sprintf(b,"^%s~%s^",c1,c2);
			pt->midstate = name_create(b);
			free(b);
		}

		head1 = head_table_insert(&mc_heads,
			head_create(pt->to_state,pt->to_stack1));
		head2 = head_table_insert(&mc_heads,
			head_create(pt->from_state,pt->from_stack));
		head_add_rule(head1,head2,pt->to_stack2,pt->b,0,pt,0,pt->vars);
	}

	pds_find_starthead(mc_pds);
}

void pds_print_trans (PDSTransition pt)
{
	printf("<%s %s> --> <%s %s %s> [%d]\n",name_cstring(pt->from_state),
		name_cstring(pt->from_stack), name_cstring(pt->to_state),
		name_cstring(pt->to_stack1), name_cstring(pt->to_stack2),
		pt->prio);
}

Name reach_target_state;
Name reach_target_stack;

void pds_add_reach_target (PushdownSystem *pds, char *target_label)
{
	Name state, stack = 0, target;
	char *copy = strdup(target_label);
	char *divide = strchr(copy,':');
	bp_fun_t fun;

	if (!divide && !mc_bp)
		common_error("reachability target must be of the form %s",
			mc_bp? "fun:label" : "state:stack_symbol");

	if (!mc_bp)
	{
		*divide = 0;
		state = name_create(copy);
		stack = name_create(divide+1);
	}
	else
	{
		char tmps[256];	// fixme
		state = bp_qstate;
		bp_reach_target_label = name_create(copy);
		for (fun = bp_functions; fun; fun = fun->next)
		{
			sprintf(tmps,"%s:%s",name_cstring(fun->funname),copy);
			stack = name_create(tmps);
			if (bp_lookup(bp_labeltree,stack,-2)) break;
		}
		if (!fun) common_error("label %s not found",copy);
		if (mc_verbose) printf("target label is %s\n",name_cstring(stack));
	}

	free(copy);

	target = name_create("$target");
	if (mc_poststar)
	{
		pds_insert_trans(pds,state,stack,target,stack,0,
				fullset,"target reached",0);
		pds_insert_trans(pds,target,stack,target,stack,0,
				fullset,NULL,0);
	}
	else
	{
		pds_insert_trans(pds,target,mc_pds.start_stack->name,
			mc_pds.start_state,mc_pds.start_stack->name,0,
				fullset,"beginning reached",0);

		reach_target_state = state;
		reach_target_stack = stack;
	}
}
