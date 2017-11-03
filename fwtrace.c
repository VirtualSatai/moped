/* =========================================================================

   Find an error trace in the automaton resulting from the post* method

   ====================================================================== */

#include <stdio.h>
#include <string.h>
#include "ba.h"
#include "mcheck.h"
#include "common.h"

#define trace_find_one(bdd,useq,name) \
	(mc_bp? bp_find_one(bdd,useq,name) : find_one(bdd,useq))
//#define trace_find_one(bdd,useq,name) find_one(bdd,useq)

void output_path_post (Path p)
{
	DdNode *tmp0, *tmp1;
	char *state;

	state = strdup(name_cstring(p->t->from_state));
	if (!mc_reach) *strchr(state,'.') = 0;
	printf("%s",state + !mc_reach);

	/* tmp0 = ex q,y',y''': p->bdd */
	Cudd_Ref(tmp0 = Cudd_bddExistAbstract(mc_mgr,p->bdd,mc_cube7));
	if (tmp0 != fullset) print_bdd(tmp0,post_trans_set,0,0,0,0);
	Cudd_RecursiveDeref(mc_mgr,tmp0);

	printf(" <");
	free(state);

	while (p)
	{
	    printf("%s",name_cstring(p->t->name));

	    /* tmp0 = ex p,y,p',q,y''': p->bdd */
	    Cudd_Ref(tmp0 = Cudd_bddExistAbstract(mc_mgr,p->bdd,mc_cube1));
	    Cudd_Ref(tmp1 = Cudd_bddExistAbstract(mc_mgr,tmp0,mc_cube8));
	    Cudd_RecursiveDeref(mc_mgr,tmp0);
	    Cudd_Ref(tmp0 = Cudd_bddExistAbstract(mc_mgr,tmp1,mc_cube9));
	    Cudd_RecursiveDeref(mc_mgr,tmp1);
	    if (tmp0 != fullset)
		print_bdd(tmp0,post_trans_set,0,p->t->name,0,0);
	    Cudd_RecursiveDeref(mc_mgr,tmp0);

	    printf((p = p->next)? " " : ">\n");
	}
}

void trace_print_transition (PDSTransition pt)
{
	int silent = (pt && pt->label && !*pt->label) * (-2);
	if (pt && pt->label && !silent) printf("  [ %s ]\n",pt->label);
}

Path trace_step_cleanup (Path p)
{
	Path p1 = p->nextconf, p2;
	int rc = (p->next && p->next->next == p1->next)? 2 : 1;

	trace_print_transition(p1->l->pt);

	while (rc > 0)
	{
		p2 = p->next;
		Cudd_RecursiveDeref(mc_mgr,p->bdd);
		free(p);
		p = p2;
		rc--;
	}

	return p1;
}

void trace_set_origin (Path p)
{
	OriginList l;
	DdNode *tmp0;

	for (l = p->t->origin; l; l = l->next)
	{
		Cudd_Ref(tmp0 = Cudd_bddAnd(mc_mgr,p->bdd,l->bdd));
		if (tmp0 == emptyset) continue;
		Cudd_RecursiveDeref(mc_mgr,tmp0);
		p->l = l;
	}
}

Path trace_step_back (Path p)
{
	OriginList l1, l2, thel1 = NULL, thel2 = NULL;
	FATransition newt1, newt2;
	PDSTransition pt = p->l->pt;
	DdNode *tmp0, *tmp1, *tmp2, *tmp3, *tmp4, *tmp5, *thetmp0;
	Path p1, p2;
	int age1, age2;

	if (!pt->to_stack1)	/* pt = <p',y'> -> <p,eps> */
	{
		/* tmp1 = ex p: p->bdd(p'->p,y'->y) /\ pt->vars */
		Cudd_Ref(tmp0 = Cudd_bddPermute(mc_mgr,p->bdd,mc_perm1));
		Cudd_Ref(tmp1
			= Cudd_bddAndAbstract(mc_mgr,tmp0,pt->vars,mc_cube10));
		Cudd_RecursiveDeref(mc_mgr,tmp0);

		/* newt1 = (p',y',mid) */
		newt1 = fatrans_table_find(p_trans,fatrans_create
			 (pt->from_state,pt->from_stack,p->l->midstate,0));
		/* newt2 = (p',y',mid) */
		newt2 = fatrans_table_find(p_trans,fatrans_create
			 (p->l->midstate,p->t->name,p->t->to_state,0));

		/* tmp2 = ex y,q,y''': tmp1 */
		Cudd_Ref(tmp0 = Cudd_bddExistAbstract(mc_mgr,tmp1,mc_cube1));
		Cudd_Ref(tmp2 = Cudd_bddExistAbstract(mc_mgr,tmp0,mc_cube8));
		Cudd_RecursiveDeref(mc_mgr,tmp0);

		/* tmp3 = (ex p'y': tmp1)(y->y') */
		Cudd_Ref(tmp0 = Cudd_bddExistAbstract(mc_mgr,tmp1,mc_cube3));
		Cudd_RecursiveDeref(mc_mgr,tmp1);
		Cudd_Ref(tmp3 = Cudd_bddPermute(mc_mgr,tmp0,mc_perm6));
		Cudd_RecursiveDeref(mc_mgr,tmp0);

		/* just to assuage the compiler */
		l1 = NULL; tmp4 = tmp5 = emptyset;

		age2 = p->l->n;
		age1 = p->l->n;
		Cudd_Ref(thetmp0 = emptyset);

		for (l2 = newt2->origin; l2; l2 = l2->next)
		{
		    if (l2->n > age2) continue;

		    /* tmp4 = ex y',q,y''': l2->bdd /\ tmp3 */
		    Cudd_Ref(tmp4
			   = Cudd_bddAndAbstract(mc_mgr,l2->bdd,tmp3,mc_cube7));

		    if (tmp4 == emptyset) continue;

		    for (l1 = newt1->origin; l1; l1 = l1->next)
		    {
			if (l1->n > p->l->n) continue;
			if (l2->n == age2 && l1->n > age1) continue;

			/* tmp5 = (ex p',y': l1->bdd /\ tmp2)(q->p,y'''->y) */
			Cudd_Ref(tmp0
			   = Cudd_bddAndAbstract(mc_mgr,l1->bdd,tmp2,mc_cube3));
			Cudd_Ref(tmp5 = Cudd_bddPermute(mc_mgr,tmp0,mc_perm11));
			Cudd_RecursiveDeref(mc_mgr,tmp0);

			Cudd_Ref(tmp0 = Cudd_bddAnd(mc_mgr,tmp4,tmp5));
			if (tmp0 != emptyset) 
			{
			    thel1 = l1;   thel2 = l2;
			    age1 = l1->n; age2 = l2->n;
			    Cudd_RecursiveDeref(mc_mgr,thetmp0);
			    thetmp0 = tmp0;
			    Cudd_RecursiveDeref(mc_mgr,tmp5);
			    Cudd_RecursiveDeref(mc_mgr,tmp4);
			    goto raus;
			}
				
			Cudd_RecursiveDeref(mc_mgr,tmp5);
		    }
		    Cudd_RecursiveDeref(mc_mgr,tmp4);
		}

raus:
		/* tmp1 = find_one[py](tmp4 /\ tmp5) */
		Cudd_Ref(tmp1 = trace_find_one(thetmp0,0,newt2->name));
		Cudd_RecursiveDeref(mc_mgr,thetmp0);

		/* tmp0 = find_one[pyy'qy'''](l2->bdd /\ tmp3 /\ tmp1) */
		Cudd_Ref(tmp0 = Cudd_bddAnd(mc_mgr,thel2->bdd,tmp3));
		Cudd_RecursiveDeref(mc_mgr,tmp3);
		Cudd_Ref(tmp3 = Cudd_bddAnd(mc_mgr,tmp0,tmp1));
		Cudd_RecursiveDeref(mc_mgr,tmp0);
		Cudd_Ref(tmp0 = trace_find_one(tmp3,5,newt2->name));
		Cudd_RecursiveDeref(mc_mgr,tmp3);

		p2 = malloc(sizeof(struct PathElementStruct));
		p2->t = newt2;
		p2->bdd = tmp0;
		p2->l = thel2;
		p2->next = p->next;

		/* tmp0 = find_one[p'y'qy''']
				(l1->bdd /\ tmp2 /\ tmp1(p->q,y->y''') */
		Cudd_Ref(tmp0 = Cudd_bddPermute(mc_mgr,tmp1,mc_perm13));
		Cudd_RecursiveDeref(mc_mgr,tmp1);
		Cudd_Ref(tmp1 = Cudd_bddAnd(mc_mgr,thel1->bdd,tmp2));
		Cudd_RecursiveDeref(mc_mgr,tmp2);
		Cudd_Ref(tmp2 = Cudd_bddAnd(mc_mgr,tmp1,tmp0));
		Cudd_RecursiveDeref(mc_mgr,tmp1);
		Cudd_RecursiveDeref(mc_mgr,tmp0);
		Cudd_Ref(tmp0 = trace_find_one(tmp2,4,newt1->name));

		p1 = malloc(sizeof(struct PathElementStruct));
		p1->t = newt1;
		p1->bdd = tmp0;
		p1->l = thel1;
		p1->next = p2;
	}
	else if (!pt->to_stack2)
	{
		/* tmp1 = ex p,y: p->bdd(p'->p,y'->y) /\ pt->vars */
		Cudd_Ref(tmp0 = Cudd_bddPermute(mc_mgr,p->bdd,mc_perm1));
		Cudd_Ref(tmp1
			= Cudd_bddAndAbstract(mc_mgr,pt->vars,tmp0,mc_cube1));
		Cudd_RecursiveDeref(mc_mgr,tmp0);

		newt1 = fatrans_table_find(p_trans,fatrans_create
			 (pt->from_state,pt->from_stack,p->t->to_state,0));

		age1 = p->l->n;
		Cudd_Ref(thetmp0 = emptyset);

		for (l1 = newt1->origin; l1; l1 = l1->next)
		{
		    if (l1->n >= age1) continue;

		    Cudd_Ref(tmp0 = Cudd_bddAnd(mc_mgr,l1->bdd,tmp1));
		    if (tmp0 != emptyset)
			{
				age1 = l1->n;
				thel1 = l1;
				Cudd_RecursiveDeref(mc_mgr,thetmp0);
				thetmp0 = tmp0;
				break;
			}
		}

		/* tmp1 = find_one[p'y'qy'''](thetmp0) */
		Cudd_RecursiveDeref(mc_mgr,tmp1);
		Cudd_Ref(tmp1 = trace_find_one(thetmp0,4,newt1->name));
		Cudd_RecursiveDeref(mc_mgr,thetmp0);

		p1 = malloc(sizeof(struct PathElementStruct));
		p1->t = newt1;
		p1->bdd = tmp1;
		p1->l = thel1;
		p1->next = p->next;
	}
	else
	{
		pt = p->next->l->pt;

		/* tmp0 = ex p,y,y'': p->next->bdd(y'->y'') */
		Cudd_Ref(tmp0 = Cudd_bddPermute(mc_mgr,p->next->bdd,mc_perm14));
		Cudd_Ref(tmp1
			= Cudd_bddAndAbstract(mc_mgr,tmp0,pt->vars,mc_cube1));
		Cudd_RecursiveDeref(mc_mgr,tmp0);
		Cudd_Ref(tmp0 = Cudd_bddExistAbstract(mc_mgr,tmp1,mc_cube6));
		Cudd_RecursiveDeref(mc_mgr,tmp1);

		newt1 = fatrans_table_find(p_trans, fatrans_create
			(pt->from_state,pt->from_stack,p->next->t->to_state,0));

		age1 = p->next->l->n;
		Cudd_Ref(thetmp0 = emptyset);

		for (l1 = newt1->origin; l1; l1 = l1->next)
		{
		    if (l1->n > age1) continue;

		    Cudd_Ref(tmp1 = Cudd_bddAnd(mc_mgr,l1->bdd,tmp0));

			if (tmp1 != emptyset)
			{
				age1 = l1->n;
				thel1 = l1;
				Cudd_RecursiveDeref(mc_mgr,thetmp0);
				thetmp0 = tmp1;
				break;
			}
		}

		/* tmp0 = find_one[p'y'qy'''](thetmp0) */
		Cudd_RecursiveDeref(mc_mgr,tmp0);
		Cudd_Ref(tmp0 = trace_find_one(thetmp0,4,newt1->name));
		Cudd_RecursiveDeref(mc_mgr,thetmp0);

		p1 = malloc(sizeof(struct PathElementStruct));
		p1->t = newt1;
		p1->bdd = tmp0;
		p1->l = thel1;
		p1->next = p->next->next;
	}

	return p1;
}


void trace_lstep_simple (Path p, Rule rule, DdNode *sb)
{
	PDSTransition pt = rule->origin;
	DdNode *tmp0, *tmp1;
	Path np;

	/* tmp1 = ex p',y': p->bdd /\ pt->vars /\ sb */
	Cudd_Ref(tmp0 = Cudd_bddAndAbstract(mc_mgr,p->bdd,rule->vars,mc_cube3));
	Cudd_RecursiveDeref(mc_mgr,p->bdd);
	Cudd_Ref(tmp1 = Cudd_bddAnd(mc_mgr,tmp0,sb));
	Cudd_RecursiveDeref(mc_mgr,tmp0);

	if (!pt->to_stack2)
	{
		p->t = fatrans_table_find(p_trans, fatrans_create
		   (rule->headfwd->state,rule->headfwd->name,p->t->to_state,0));

		/* p->bdd = find_one[p'y'qy'''](tmp0(p->p',y->y')) */
		Cudd_Ref(tmp0 = Cudd_bddPermute(mc_mgr,tmp1,mc_perm6));
		Cudd_RecursiveDeref(mc_mgr,tmp1);
		Cudd_Ref(p->bdd = trace_find_one(tmp0,4,p->t->name));
		Cudd_RecursiveDeref(mc_mgr,tmp0);
		trace_set_origin(p);
	}
	else
	{
		np = common_malloc(sizeof(struct PathElementStruct));
		np->t = fatrans_table_find(p_trans, fatrans_create
			(pt->midstate,pt->to_stack2,p->t->to_state,0));
		np->next = p->next;
		p->t = fatrans_table_find(p_trans, fatrans_create
			(pt->to_state,pt->to_stack1,pt->midstate,0));
		p->next = np;

		/* np->bdd = find_one[pyy'qy''](tmp1(y''->y') */
		Cudd_Ref(tmp0 = Cudd_bddPermute(mc_mgr,tmp1,mc_perm10));
		Cudd_RecursiveDeref(mc_mgr,tmp1);
		Cudd_Ref(np->bdd = trace_find_one(tmp0,5,np->t->name));
		Cudd_RecursiveDeref(mc_mgr,tmp0);

		/* p->bdd = (ex q',y',y''': np->bdd)(p->p',y->y')
					/\ (p'=q) /\ (y'=y''') */
		Cudd_Ref(tmp0 = Cudd_bddExistAbstract(mc_mgr,np->bdd,mc_cube7));
		Cudd_Ref(tmp1 = Cudd_bddPermute(mc_mgr,tmp0,mc_perm6));
		Cudd_RecursiveDeref(mc_mgr,tmp0);
		Cudd_Ref(p->bdd = Cudd_bddAnd(mc_mgr,tmp1,mc_qyeqv));
		Cudd_RecursiveDeref(mc_mgr,tmp1);
	}
}

Path trace_loop_post (Path p, Rule r, DdNode *sb)
{
	DdNode *tmp0, *tmp1, *tmp2;
	Path bp, p1, p2;
	Head head;
	Rule r1;

	if (!r->new)
	{
		trace_print_transition(r->origin);
		trace_lstep_simple(p,r,sb);
		output_path_post(p);
		return p;
	}

	bp = common_malloc(sizeof(struct PathElementStruct));
	bp->t = p->t;
	Cudd_Ref(bp->bdd = p->bdd);
	bp->next = p->next;

	trace_lstep_simple(p,r,sb);

	p1 = common_malloc(sizeof(struct PathElementStruct));
	p2 = common_malloc(sizeof(struct PathElementStruct));
	head = get_head_from_state(r->midstate);

	for (r1 = head->rules, tmp1 = NULL; r1; r1 = r1->next)
	{
		if (r1->head != r->head || r1->tail != p->t->name) continue;

		p1->t = fatrans_table_find(p_trans, fatrans_create
			(r->origin->from_state,r->origin->from_stack,
			 r->midstate,0));
		p2->t = fatrans_table_find(p_trans, fatrans_create
			(r->midstate,p->t->name,p->t->to_state,0));

		/* tmp0 = ex p',y': bp->bdd /\ r1->vars */
		Cudd_Ref(tmp0 = Cudd_bddAndAbstract
			(mc_mgr,bp->bdd,r1->origin->vars,mc_cube3));

		/* tmp2 = (ex p': p->bdd)(y'->y'') */
		Cudd_Ref(tmp1 = Cudd_bddExistAbstract(mc_mgr,p->bdd,mc_cube9));
		Cudd_Ref(tmp2 = Cudd_bddPermute(mc_mgr,tmp1,mc_perm14));
		Cudd_RecursiveDeref(mc_mgr,tmp1);

		/* tmp1 = tmp0 /\ tmp2 */
		Cudd_Ref(tmp1 = Cudd_bddAnd(mc_mgr,tmp0,tmp2));
		Cudd_RecursiveDeref(mc_mgr,tmp0);
		Cudd_RecursiveDeref(mc_mgr,tmp2);

		/* tmp0 = p1->t->rel(q->p,y'''->y) */
		Cudd_Ref(tmp0 = Cudd_bddPermute(mc_mgr,p1->t->rel,mc_perm11));

		/* tmp2 = tmp0 /\ tmp1 */
		Cudd_Ref(tmp2 = Cudd_bddAnd(mc_mgr,tmp0,tmp1));
		Cudd_RecursiveDeref(mc_mgr,tmp0);
		Cudd_RecursiveDeref(mc_mgr,tmp1);

		/* tmp0 = ex p: r->vars /\ (ex q,y',y'': p->bdd)(p'->p) */
		Cudd_Ref(tmp0 = Cudd_bddExistAbstract(mc_mgr,p->bdd,mc_cube7));
		Cudd_Ref(tmp1 = Cudd_bddPermute(mc_mgr,tmp0,mc_perm1));
		Cudd_RecursiveDeref(mc_mgr,tmp0);
		Cudd_Ref(tmp0 = Cudd_bddAndAbstract
			(mc_mgr,r->origin->vars,tmp1,mc_cube10));
		Cudd_RecursiveDeref(mc_mgr,tmp1);

		/* tmp1 = tmp0 /\ tmp2 */
		Cudd_Ref(tmp1 = Cudd_bddAnd(mc_mgr,tmp0,tmp2));
		Cudd_RecursiveDeref(mc_mgr,tmp0);
		Cudd_RecursiveDeref(mc_mgr,tmp2);

		if (tmp1 != emptyset) break;
	}

	/* p1->bdd = (ex y'',q,y''': tmp1)(p->q,y->y''') */
	Cudd_Ref(tmp0 = Cudd_bddExistAbstract(mc_mgr,tmp1,mc_cube6));
	Cudd_Ref(tmp2 = Cudd_bddExistAbstract(mc_mgr,tmp0,mc_cube8));
	Cudd_RecursiveDeref(mc_mgr,tmp0);
	Cudd_Ref(p1->bdd = Cudd_bddPermute(mc_mgr,tmp2,mc_perm13));
	Cudd_RecursiveDeref(mc_mgr,tmp2);

	/* p2->bdd = (ex p',y': tmp1)(y''->y') */
	Cudd_Ref(tmp2 = Cudd_bddExistAbstract(mc_mgr,tmp1,mc_cube3));
	Cudd_RecursiveDeref(mc_mgr,tmp1);
	Cudd_Ref(p2->bdd = Cudd_bddPermute(mc_mgr,tmp2,mc_perm10));
	Cudd_RecursiveDeref(mc_mgr,tmp2);

	Cudd_RecursiveDeref(mc_mgr,bp->bdd);
	free(bp);

	trace_set_origin(p1);
	trace_set_origin(p2);
	p1->next = p2;
	p2->next = p->next;
	p1->nextconf = p;

	while (p1->next != p->next)
	{
		p2 = trace_step_back(p1);
		p2->nextconf = p1;
		p1 = p2;
	}

	trace_print_transition(r1->origin);
	p1 = p1->nextconf;
	while (p1->nextconf)
	{
		output_path_post(p1);
		p1 = trace_step_cleanup(p1);
	}
	output_path_post(p1);

	return p1;
}

Path find_edge (Name state, Name stack, DdNode *bdd, int age)
{
	FATransition t, t1 = NULL, thead;
	DdNode *tmp0, *tmp1;
	OriginList l, l1 = NULL;
	Path p;

	thead = fatrans_table_find(p_index,fatrans_create(state,stack,0,0));

	Cudd_Ref(tmp1 = emptyset);
	if (thead)
	{
		for (t = thead->list; t; t = t->list)
		{
			for (l = t->origin; l; l = l->next)
			{
				if (age >= 0 && l->n > age) continue;

				Cudd_Ref(tmp0 = Cudd_bddAnd(mc_mgr,bdd,l->bdd));
				if (tmp0 == emptyset) continue;

				age = l->n;
				Cudd_RecursiveDeref(mc_mgr,tmp1);
				tmp1 = tmp0;
				t1 = t;
				l1 = l;
			}
		}
	}
	p = malloc(sizeof(struct PathElementStruct));
	p->t = t1;
	Cudd_Ref(p->bdd = trace_find_one(tmp1,stack? 4 : 5,p->t->name));
	p->l = l1;
	p->next = NULL;
	return p;
}

Path find_conf (Head head)
{
	Path result, last, new;
	DdNode *tmp0, *tmp1;

	/* tmp0 = head->trans(p->p',y->y') */
	Cudd_Ref(tmp0 = Cudd_bddPermute(mc_mgr,head->trans,mc_perm6));
	Cudd_RecursiveDeref(mc_mgr,head->trans);

	result = last = find_edge(head->state,head->name,tmp0,-1);
	Cudd_RecursiveDeref(mc_mgr,tmp0);

	while (last->t->to_state != mc_sstate)
	{
	    /* tmp0 = (ex p,y,p',y': last->bdd)(q->p,y'''->y) */
	    Cudd_Ref(tmp0 = Cudd_bddExistAbstract(mc_mgr,last->bdd,mc_cube1));
	    Cudd_Ref(tmp1 = Cudd_bddExistAbstract(mc_mgr,tmp0,mc_cube3));
	    Cudd_RecursiveDeref(mc_mgr,tmp0);
	    Cudd_Ref(tmp0 = Cudd_bddPermute(mc_mgr,tmp1,mc_perm11));
	    Cudd_RecursiveDeref(mc_mgr,tmp1);
	    new = find_edge(last->t->to_state,0,tmp0,last->l->n);
	    Cudd_RecursiveDeref(mc_mgr,tmp0);
	    last->next = new;
	    last = last->next;
	}

	result->nextconf = NULL;

	/* head->trans = (ex q,y''': path->bdd)(p'->p,y'->y) */
	Cudd_Ref(tmp0 = Cudd_bddExistAbstract(mc_mgr,result->bdd,mc_cube8));
	Cudd_Ref(tmp1 = Cudd_bddPermute(mc_mgr,tmp0,mc_perm1));
	Cudd_RecursiveDeref(mc_mgr,tmp0);
	head->trans = tmp1;

	return result;
}

extern void print_shuffle();

void get_post_trace (Head cycle)
{
	Path path, p1;
	int count = 0;
	
	find_one_init();

	path = find_conf(cycle);

	while (path->l->pt)
	{
		p1 = trace_step_back(path);
		p1->nextconf = path;
		path->prevconf = p1;
		path = p1;
		count++;
	}
	path->prevconf = NULL;

	if (mc_bp && mc_reach && mc_trace > 1)
	{
		if (mc_trace == 2) bp_get_trace_newton(path,1);
		if (mc_trace == 3) bp_get_trace_xml(path,1);
		return;
	}

	printf("\n--- START ---\n");

	while (path->nextconf)
	{
		output_path_post(path);
		path = trace_step_cleanup(path);
	}
		
	if (mc_reach) return;
	output_path_post(path);
	printf("\n--- LOOP ---\n");

	cycle->dfsnum = -1;
	trace_findloop(&path,cycle,cycle->trans,0,trace_loop_post);
}
