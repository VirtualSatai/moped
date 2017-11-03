/* =========================================================================

   Analyse the automaton resulting from the pre* method

   ====================================================================== */

#include <stdio.h>
#include <string.h>
#include "ba.h"
#include "mcheck.h"
#include "common.h"

void output_path_pre (Path p)
{
	DdNode *tmp0;
	char *state;

	state = strdup(name_cstring(p->t->from_state));
	if (!mc_reach) *strchr(state,'.') = 0;
	printf("%s",state + !mc_reach);

	/* tmp0 = ex q,y: p->bdd */
	Cudd_Ref(tmp0 = Cudd_bddExistAbstract(mc_mgr,p->bdd,mc_cube4));
	if (tmp0 != fullset) print_bdd(tmp0,fatrans_set,0,0,0,0);
	Cudd_RecursiveDeref(mc_mgr,tmp0);

	printf(" <");
	free(state);

	while (p)
	{
	    printf("%s",name_cstring(p->t->name));

	    /* tmp0 = ex p,q: p->bdd */
	    Cudd_Ref(tmp0 = Cudd_bddExistAbstract(mc_mgr,p->bdd,mc_cube5));
	    if (tmp0 != fullset) print_bdd(tmp0,fatrans_set,p->t->name,0,0,0);
	    Cudd_RecursiveDeref(mc_mgr,tmp0);

	    printf((p = p->next)? " " : ">\n");
	}
}


/* Restrict orig to the contents of l with are older than limit */

DdNode* restrict_old (DdNode *orig, OriginList l, int limit)
{
	DdNode *tmp0, *tmp1, *tmp2;

	Cudd_Ref(tmp0 = emptyset);
	for (; l; l = l->next)
	{
		if (l->n >= limit) continue;
		Cudd_Ref(tmp1 = Cudd_bddAnd(mc_mgr,orig,l->bdd));
		if (tmp1 == emptyset) continue;

		Cudd_Ref(tmp2 = Cudd_bddOr(mc_mgr,tmp0,tmp1));
		Cudd_RecursiveDeref(mc_mgr,tmp0);
		Cudd_RecursiveDeref(mc_mgr,tmp1);
		tmp0 = tmp2;
	}
	Cudd_RecursiveDeref(mc_mgr,orig);

	return tmp0;
}

int trace_findstack (Path *result, Name state, DdNode *bdd, NameStack stack)
{
	FATransition t, thead;
	DdNode *tmp0, *tmp1;
	char success;

	if (bdd && bdd == emptyset) { *result = NULL; return 0; }
	if (!stack) { *result = NULL; return state == mc_sstate; }

	*result = common_malloc(sizeof(struct PathElementStruct));
	if (state == mc_sstate)
	{
		(*result)->t = fatrans_create
				(mc_sstate,stack->name,mc_sstate,0);
		(*result)->bdd = fullset;
		trace_findstack(&((*result)->next),mc_sstate,NULL,stack->next);
		return 1;
	}

	thead = fatrans_table_find(mc_index,
			fatrans_create(state,stack->name,0,0));

	if (thead) for (t = thead->list; t != LIST_END; t = t->list)
	{
		(*result)->t = t;

		/* tmp1 = state /\ stack /\ t->rel */
		Cudd_Ref(tmp0 = Cudd_bddAnd(mc_mgr,bdd,stack->bdd));
		Cudd_Ref(tmp1 = Cudd_bddAnd(mc_mgr,tmp0,t->rel));
		Cudd_RecursiveDeref(mc_mgr,tmp0);
		(*result)->bdd = tmp1;

		/* tmp1 = (ex p,y: tmp1)(q->p) */
		Cudd_Ref(tmp0 = Cudd_bddExistAbstract(mc_mgr,tmp1,mc_cube1));
		Cudd_Ref(tmp1 = Cudd_bddPermute(mc_mgr,tmp0,mc_perm2));
		Cudd_RecursiveDeref(mc_mgr,tmp0);

		success = trace_findstack(&((*result)->next),
					t->to_state,tmp1,stack->next);

		Cudd_RecursiveDeref(mc_mgr,tmp1);

		if (!success)
		{
			Cudd_RecursiveDeref(mc_mgr,(*result)->bdd);
			continue;
		}

		if ((*result)->next)
		{
		    /* result->bdd /\= (ex q,y: result->next)(p->q) */
		    Cudd_Ref(tmp0 = Cudd_bddExistAbstract
				    (mc_mgr,(*result)->next->bdd,mc_cube4));
		    Cudd_Ref(tmp1 = Cudd_bddPermute(mc_mgr,tmp0,mc_perm3));
		    Cudd_RecursiveDeref(mc_mgr,tmp0);
		    Cudd_Ref(tmp0 = Cudd_bddAnd(mc_mgr,(*result)->bdd,tmp1));
		    Cudd_RecursiveDeref(mc_mgr,tmp1);
		    Cudd_RecursiveDeref(mc_mgr,(*result)->bdd);
		}
		else
		{
		    tmp0 = (*result)->bdd;
		}

		if (tmp0 == emptyset) continue;

		Cudd_Ref((*result)->bdd 
				= find_one(tmp0,t->to_state != mc_sstate));
		Cudd_RecursiveDeref(mc_mgr,tmp0);
		return 1;
	}

	common_free(*result,sizeof(struct PathElementStruct));
	return 0;
}

OriginList find_origin (OriginList l, DdNode *bdd)
{
	DdNode *tmp0;

	while (l)
	{
		if (!l->pt) return l;
		Cudd_Ref(tmp0 = Cudd_bddAnd(mc_mgr,l->bdd,bdd));
		if (tmp0 == emptyset) { l = l->next; continue; }
		Cudd_RecursiveDeref(mc_mgr,tmp0);
		return l;
	}
	return NULL;
}

Path trace_step_pre (Path p)
{
	FATransition newt;
	DdNode *tmp0, *tmp1, *tmp2, *tmp3;
	Path np;

	p->l = find_origin(p->t->origin,p->bdd);
	if (!p->l->pt) return NULL;
	
	np = common_malloc(sizeof(struct PathElementStruct));
	memcpy(np,p,sizeof(struct PathElementStruct));
	p = np;
	
	if (!p->l->pt->to_stack1)
	{
		np = p->next;
		p->t = np->t;
//		Cudd_RecursiveDeref(mc_mgr,p->bdd);
		p->bdd = np->bdd;
		p->next = np->next;
//		common_free(np,sizeof(struct PathElementStruct));
	}
	else if (!p->l->pt->to_stack2)
	{
		/* p->bdd = find_one[pyq](restrict(
			(ex p',y': p->bdd(p->p',y->y') /\ p->l->pt->vars)) */

		newt = fatrans_table_find(mc_trans,fatrans_create
			 (p->l->pt->to_state,p->l->pt->to_stack1,p->t->to_state,0));

		Cudd_Ref(tmp0 = Cudd_bddPermute(mc_mgr,p->bdd,mc_perm6));
//		Cudd_RecursiveDeref(mc_mgr,p->bdd);
		Cudd_Ref(tmp1 = Cudd_bddAndAbstract
					(mc_mgr,tmp0,p->l->pt->vars,mc_cube3));
		Cudd_RecursiveDeref(mc_mgr,tmp0);

		p->t = newt;
		tmp0 = restrict_old(tmp1,newt->origin,p->l->n);
		Cudd_Ref(p->bdd = find_one(tmp0,p->t->to_state != mc_sstate));
		Cudd_RecursiveDeref(mc_mgr,tmp0);
	}
	else
	{
		np = common_malloc(sizeof(struct PathElementStruct));

		newt = fatrans_table_find(mc_trans, fatrans_create
			 (p->l->pt->to_state,p->l->pt->to_stack1,p->l->midstate,0));

		/* tmp1 = ex p',y': p->bdd(p->p',y->y') /\ p->l->pt->vars */
		Cudd_Ref(tmp0 = Cudd_bddPermute(mc_mgr,p->bdd,mc_perm6));
//		Cudd_RecursiveDeref(mc_mgr,p->bdd);
		Cudd_Ref(tmp1 = Cudd_bddAndAbstract
					(mc_mgr,tmp0,p->l->pt->vars,mc_cube3));
		Cudd_RecursiveDeref(mc_mgr,tmp0);

		if (p->l->midstate == mc_sstate)
		{
		    np->t = fatrans_create
				(mc_sstate,p->l->pt->to_stack2,mc_sstate,0);
		    np->bdd = fullset;	/* let's ignore the values here
						because we'll never get back */

		    /* p->bdd = find_one[py](restrict(ex y'': tmp1)) */
		    Cudd_Ref(tmp0=Cudd_bddExistAbstract(mc_mgr,tmp1,mc_cube3));
		    Cudd_RecursiveDeref(mc_mgr,tmp1);
		    tmp2 = restrict_old(tmp0,newt->origin,p->l->n);

		    Cudd_Ref(p->bdd = find_one(tmp2,0));
		    Cudd_RecursiveDeref(mc_mgr,tmp2);
		}
		else
		{
		    np->t = fatrans_table_find(mc_trans,fatrans_create
		       (p->l->midstate,p->l->pt->to_stack2,p->t->to_state,0));

		    /* tmp3 = tmp1 /\ newt->rel(q->p')
				   /\ np->t->rel(p->p',y->y'') */
		    Cudd_Ref(tmp0 = Cudd_bddPermute(mc_mgr,newt->rel,mc_perm7));
		    Cudd_Ref(tmp2 = Cudd_bddAnd(mc_mgr,tmp1,tmp0));
		    Cudd_RecursiveDeref(mc_mgr,tmp0);
		    Cudd_RecursiveDeref(mc_mgr,tmp1);
		    Cudd_Ref(tmp0=Cudd_bddPermute(mc_mgr,np->t->rel,mc_perm8));
		    Cudd_Ref(tmp3 = Cudd_bddAnd(mc_mgr,tmp2,tmp0));
		    Cudd_RecursiveDeref(mc_mgr,tmp0);
		    Cudd_RecursiveDeref(mc_mgr,tmp2);

		    /* tmp2 = res((ex q,y'': tmp3)(p'->q) /\ newt->rel) */
		    Cudd_Ref(tmp1=Cudd_bddExistAbstract(mc_mgr,tmp3,mc_cube2));
		    Cudd_Ref(tmp0 = Cudd_bddPermute(mc_mgr,tmp1,mc_perm4));
		    Cudd_RecursiveDeref(mc_mgr,tmp1);
		    tmp2 = restrict_old(tmp0,newt->origin,p->l->n);

		    /* tmp1 = res((ex p,y: tmp3)(p'->p,y''->y) /\ np->t->rel) */
		    Cudd_Ref(tmp1=Cudd_bddExistAbstract(mc_mgr,tmp3,mc_cube1));
		    Cudd_RecursiveDeref(mc_mgr,tmp3);
		    Cudd_Ref(tmp0 = Cudd_bddPermute(mc_mgr,tmp1,mc_perm9));
		    Cudd_RecursiveDeref(mc_mgr,tmp1);
		    tmp1 = restrict_old(tmp0,np->t->origin,p->l->n);

		    /* tmp3 = find_one[pyp'y''q]
				(tmp2(q->p') /\ tmp1(p->p',y->y'') */
		    Cudd_Ref(tmp0 = Cudd_bddPermute(mc_mgr,tmp2,mc_perm7));
		    Cudd_RecursiveDeref(mc_mgr,tmp2);
		    Cudd_Ref(tmp2 = Cudd_bddPermute(mc_mgr,tmp1,mc_perm8));
		    Cudd_RecursiveDeref(mc_mgr,tmp1);
		    Cudd_Ref(tmp1 = Cudd_bddAnd(mc_mgr,tmp0,tmp2));
		    Cudd_RecursiveDeref(mc_mgr,tmp0);
		    Cudd_RecursiveDeref(mc_mgr,tmp2);
		    Cudd_Ref(tmp3 = find_one(tmp1,3));
		    Cudd_RecursiveDeref(mc_mgr,tmp1);

		    /* p->bdd = (ex q,y'': tmp3)(p'->q) */
		    Cudd_Ref(tmp1=Cudd_bddExistAbstract(mc_mgr,tmp3,mc_cube2));
		    Cudd_Ref(tmp0 = Cudd_bddPermute(mc_mgr,tmp1,mc_perm4));
		    Cudd_RecursiveDeref(mc_mgr,tmp1);
		    p->bdd = tmp0;

		    /* np->bdd = (ex p,y: tmp3)(p'->p,y''->y) */
		    Cudd_Ref(tmp1=Cudd_bddExistAbstract(mc_mgr,tmp3,mc_cube1));
		    Cudd_RecursiveDeref(mc_mgr,tmp3);
		    Cudd_Ref(tmp0 = Cudd_bddPermute(mc_mgr,tmp1,mc_perm9));
		    Cudd_RecursiveDeref(mc_mgr,tmp1);
		    np->bdd = tmp0;
		}

		np->next = p->next;
		p->t = newt;
		p->next = np;
	}

	return p;
}

void trace_lstep_pre (Path p, Rule rule, DdNode *sb)
{
	PDSTransition pt = rule->origin;
	DdNode *tmp0, *tmp1, *tmp2;
	Path np;

	/* tmp1 = ex p',y': p->bdd(p->p',y->y') /\ pt->vars */
	Cudd_Ref(tmp0 = Cudd_bddPermute(mc_mgr,p->bdd,mc_perm6));
	Cudd_RecursiveDeref(mc_mgr,p->bdd);
	Cudd_Ref(tmp1 = Cudd_bddAndAbstract(mc_mgr,tmp0,pt->vars,mc_cube3));
	Cudd_RecursiveDeref(mc_mgr,tmp0);

	if (pt->label) printf("  [ %s ]\n",pt->label);

	if (!pt->to_stack2)
	{
		/* p->bdd = find_one[py](tmp1 /\ sb) */
		p->t = fatrans_table_find(mc_trans,
		    fatrans_create(pt->to_state,pt->to_stack1,mc_sstate,0));
		Cudd_Ref(tmp0 = Cudd_bddAnd(mc_mgr,tmp1,sb));
		Cudd_RecursiveDeref(mc_mgr,tmp1);
		Cudd_Ref(p->bdd = find_one(tmp0,0));
		Cudd_RecursiveDeref(mc_mgr,tmp0);
	}
	else if (rule->new)
	{
		np = common_malloc(sizeof(struct PathElementStruct));
		np->t = fatrans_table_find(mc_trans, fatrans_create
			(rule->headfwd->state,pt->to_stack2,mc_sstate,0));
		np->next = p->next;
		p->t = fatrans_table_find(mc_trans, fatrans_create
			(pt->to_state,pt->to_stack1,rule->headfwd->state,0));
		p->next = np;

		/* tmp0 = find_one[pyqy''](tmp1 /\ sb(p->q,y->y'')) */
		Cudd_Ref(tmp0 = Cudd_bddPermute(mc_mgr,sb,mc_perm3));
		Cudd_Ref(tmp2 = Cudd_bddAnd(mc_mgr,tmp1,tmp0));
		Cudd_RecursiveDeref(mc_mgr,tmp0);
		Cudd_RecursiveDeref(mc_mgr,tmp1);
		Cudd_Ref(tmp0 = find_one(tmp2,2));
		Cudd_RecursiveDeref(mc_mgr,tmp2);

		/* p->bdd = ex y'': tmp0 */
		Cudd_Ref(p->bdd = Cudd_bddExistAbstract(mc_mgr,tmp0,mc_cube6));
		/* np->bdd = (ex p,y: tmp0)(q->p,y''->y) */
		Cudd_Ref(tmp1 = Cudd_bddExistAbstract(mc_mgr,tmp0,mc_cube1));
		Cudd_Ref(np->bdd = Cudd_bddPermute(mc_mgr,tmp1,mc_perm2));
	
		Cudd_RecursiveDeref(mc_mgr,tmp0);
		Cudd_RecursiveDeref(mc_mgr,tmp1);
	}
	else
	{
		np = common_malloc(sizeof(struct PathElementStruct));
		np->t = fatrans_create(mc_sstate,pt->to_stack2,mc_sstate,0);
		np->next = p->next;
		p->t = fatrans_table_find(mc_trans,
		    fatrans_create(pt->to_state,pt->to_stack1,mc_sstate,0));
		p->next = np;

		/* tmp1 = find_one[pyqy''](tmp1 /\ sb) */
		Cudd_Ref(tmp0 = Cudd_bddAnd(mc_mgr,tmp1,sb));
		Cudd_RecursiveDeref(mc_mgr,tmp1);
		Cudd_Ref(tmp1 = find_one(tmp0,2));
		Cudd_RecursiveDeref(mc_mgr,tmp0);

		/* p->bdd = ex q,y'': tmp1 */
		Cudd_Ref(p->bdd = Cudd_bddExistAbstract(mc_mgr,tmp1,mc_cube2));
		/* np->bdd = (ex p,y,q: tmp1)(y''->y) */
		Cudd_Ref(tmp0 = Cudd_bddExistAbstract(mc_mgr,tmp1,mc_cube1));
		Cudd_RecursiveDeref(mc_mgr,tmp1);
		Cudd_Ref(tmp1 = Cudd_bddExistAbstract(mc_mgr,tmp0,mc_cube5));
		Cudd_RecursiveDeref(mc_mgr,tmp0);
		Cudd_Ref(np->bdd = Cudd_bddPermute(mc_mgr,tmp1,mc_perm9));
		Cudd_RecursiveDeref(mc_mgr,tmp1);

		/* On balance, let's just set np->bdd to fullset because
		   we never come back to that point. */
		Cudd_RecursiveDeref(mc_mgr,np->bdd);
		np->bdd = fullset;
	}
}

Path trace_loop_pre (Path p, Rule r, DdNode *sb)
{
	trace_lstep_pre(p,r,sb);

	output_path_pre(p);
	while (p->t->to_state != mc_sstate)
	{
		p = trace_step_pre(p);
		if (p) output_path_pre(p);
	}

	return p;
}

void get_pre_trace ()
{
	Path path, p1, pbeg;
	Head head;
	char *answer;
	char ret;

	find_one_init();

	if (!trace_findstack(&pbeg, mc_starthead->state,
				mc_pds.start_bdd, mc_pds.start_stack))
	{
		answer = mc_reach? "NO": "YES";
		ret = 1;
	}
	else
	{
		answer = mc_reach? "YES": "NO";
		ret = !mc_trace;
	}

	printf("%s.\n",answer);
	if (mc_reach > 1) print_pre_automaton(&mc_trans);
	if (ret) return;

	printf("\n");

	(path = pbeg)->prevconf = NULL;
	while ((p1 = trace_step_pre(path)))
	{
		p1->prevconf = path;
		path->nextconf = p1;
		path = p1;
	}
	path->nextconf = NULL;

	if (mc_bp && mc_reach && mc_trace > 1)
	{
		Cudd_Ref(mc_cube8 = mc_cube2);
		if (mc_trace == 2) bp_get_trace_newton(path,0);
		if (mc_trace == 3) bp_get_trace_xml(path,0);
		return;
	}

	printf("--- START ---\n");

	for (path = pbeg; path; path = path->nextconf)
	{
		if (!mc_reach || path->nextconf) output_path_pre(path);
		if (!path->nextconf) break;
		if (path->l->pt->label)
			printf("  [ %s ]\n",path->l->pt->label);
	}

	if (mc_reach) return;

	printf("\n--- LOOP ---\n");

	head = head_find(mc_heads,path->t->from_state,path->t->name);
	Cudd_Ref(path->bdd);

	head->dfsnum = -1;
	Cudd_Ref(head->trans = path->bdd);
	trace_findloop(&path,head,path->bdd,0,trace_loop_pre);
}
