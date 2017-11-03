#include "cycle.h"
#include "common.h"

char el_method (CNode snode)
{
	DdNode *tmp0, *tmp1;
	CNode n1, cstack;
	CEdge edge;
	char found = 0, converged = 0;

	for (n1 = snode; n1; n1 = n1->next)
		Cudd_Ref(n1->z = fullset);

	while (!converged)
	{
	    /* nu Z. mu Y. EX (Z /\ c) \/ EX Y */

	    if (mc_verbose) printf("###\n");
	    init_y_stack(snode,&cstack);

	    for (n1 = snode; n1; n1 = n1->next)
	    {
		for (edge = n1->bkedges; edge; edge = edge->nextfrom)
		{
		    if (!edge->b) continue;

		    /* y = y \/ (ex p,y: edge->e /\ z)(p'->p,y'->y) */
		    Cudd_Ref(tmp0 = Cudd_bddAndAbstract
			(mc_mgr,edge->e,n1->z,mc_cube1));
		    Cudd_Ref(tmp1 = Cudd_bddPermute(mc_mgr,tmp0,mc_perm1));
		    Cudd_RecursiveDeref(mc_mgr,tmp0);

		    add_y_edge(edge->from,tmp1,&cstack);
		}
	    }

	    while (cstack)
	    {
		n1 = cstack;
		n1->flag = 0;
		cstack = cstack->stack;

		if (mc_verbose) printf("...\n");

		for (edge = n1->bkedges; edge; edge = edge->nextfrom)
		{
		    if (edge->b) continue;

		    /* y = y \/ (ex p,y: edge->e /\ y)(p'->p,y'->y) */
		    Cudd_Ref(tmp0 = Cudd_bddAndAbstract
			(mc_mgr,edge->e,n1->y,mc_cube1));
		    Cudd_Ref(tmp1 = Cudd_bddPermute(mc_mgr,tmp0,mc_perm1));
		    Cudd_RecursiveDeref(mc_mgr,tmp0);

		    add_y_edge(edge->from,tmp1,&cstack);
		}
	    }

	    converged = 1; found = 0;
	    for (n1 = snode; n1; n1 = n1->next)
	    {
		/* z = y */
		if (n1->z != n1->y) converged = 0;
		Cudd_RecursiveDeref(mc_mgr,n1->z);
		n1->z = n1->y;
		if (n1->z != emptyset) found = 1;
	    }
	}

	return found;
}

char owcty_method (CNode snode)
{
	DdNode *tmp0, *tmp1;
	CNode n1, cstack;
	CEdge edge;
	char found = 0, converged = 0;

	/* nu Z. EG mu Y. EX (Z /\ c) \/ EX Y */

	for (n1 = snode; n1; n1 = n1->next)
		Cudd_Ref(n1->z = fullset);

	while (!converged)
	{
	    if (mc_verbose) printf("###\n");
	    init_y_stack(snode,&cstack);

	    for (n1 = snode; n1; n1 = n1->next)
	    {
		Cudd_Ref(n1->x = emptyset);

		for (edge = n1->bkedges; edge; edge = edge->nextfrom)
		{
		    if (!edge->b) continue;

		    /* y = y \/ (ex p,y: edge->e /\ z)(p'->p,y'->y) */
		    Cudd_Ref(tmp0 = Cudd_bddAndAbstract
			(mc_mgr,edge->e,n1->z,mc_cube1));
		    Cudd_Ref(tmp1 = Cudd_bddPermute(mc_mgr,tmp0,mc_perm1));
		    Cudd_RecursiveDeref(mc_mgr,tmp0);

		    add_y_edge(edge->from,tmp1,&cstack);
		}
	    }

	    while (cstack)
	    {
		n1 = cstack;
		n1->flag = 0;
		cstack = cstack->stack;

		if (mc_verbose) printf("...\n");

		for (edge = n1->bkedges; edge; edge = edge->nextfrom)
		{
		    if (edge->b) continue;

		    /* y = y \/ (ex p,y: edge->e /\ y)(p'->p,y'->y) */
		    Cudd_Ref(tmp0 = Cudd_bddAndAbstract
			(mc_mgr,edge->e,n1->y,mc_cube1));
		    Cudd_Ref(tmp1 = Cudd_bddPermute(mc_mgr,tmp0,mc_perm1));
		    Cudd_RecursiveDeref(mc_mgr,tmp0);

		    add_y_edge(edge->from,tmp1,&cstack);
		}
	    }

	    while (!converged)
	    {
		if (mc_verbose) printf("---\n");

		for (n1 = snode; n1; n1 = n1->next)
		{
		    for (edge = n1->bkedges; edge; edge = edge->nextfrom)
		    {
			/* x = x \/ (ex p,y: edge->e /\ y)(p'->p,y'->y) */
			Cudd_Ref(tmp0 = Cudd_bddAndAbstract
				(mc_mgr,edge->e,n1->y,mc_cube1));
			Cudd_Ref(tmp1 = Cudd_bddPermute(mc_mgr,tmp0,mc_perm1));
			Cudd_RecursiveDeref(mc_mgr,tmp0);
			Cudd_Ref(tmp0 = Cudd_bddOr(mc_mgr,edge->from->x,tmp1));
			Cudd_RecursiveDeref(mc_mgr,tmp1);
			Cudd_RecursiveDeref(mc_mgr,edge->from->x);
			edge->from->x = tmp0;
		    }
		}
		
		converged = 1;
		for (n1 = snode; n1; n1 = n1->next)
		{
			/* y = x */
			if (n1->y != n1->x) converged = 0;
			Cudd_RecursiveDeref(mc_mgr,n1->y);
			n1->y = n1->x;
			Cudd_Ref(n1->x = emptyset);
		}
	    }

	    converged = 1; found = 0;
	    for (n1 = snode; n1; n1 = n1->next)
	    {
		/* z = y */
		if (n1->z != n1->y) converged = 0;
		Cudd_RecursiveDeref(mc_mgr,n1->x);
		Cudd_RecursiveDeref(mc_mgr,n1->z);
		n1->z = n1->y;
		if (n1->z != emptyset) found = 1;
	    }
	}

	return found;
}

void check_for_real_cycles (CNode snode, CNode n)
{
	CNode n1, cstack;
	CEdge edge;
	DdNode *tmp0, *tmp1;

	init_y_stack(snode,&cstack);

	for (edge = n->bkedges; edge; edge = edge->nextfrom)
	{
		if (!edge->b) continue;

		/* y = y \/ (n1->z /\ edge->e)(py->qy'',p'y'->py) */
		Cudd_Ref(tmp1 = Cudd_bddAnd(mc_mgr,edge->e,n->z));
		Cudd_Ref(tmp0 = Cudd_bddPermute(mc_mgr,tmp1,mc_perm3));
		Cudd_RecursiveDeref(mc_mgr,tmp1);
		Cudd_Ref(tmp1 = Cudd_bddPermute(mc_mgr,tmp0,mc_perm1));
		Cudd_RecursiveDeref(mc_mgr,tmp0);
		add_y_edge(edge->from,tmp1,&cstack);
	}

	if (mc_demand && n->y != emptyset)
	{
		Cudd_Ref(tmp0 = Cudd_bddAndAbstract
				(mc_mgr,n->y,mc_pyeqv,mc_cube2));
		if (tmp0 != emptyset)
		{
			Cudd_RecursiveDeref(mc_mgr,n->z);
			n->z = tmp0;
			goto cleanup;
		}
	}

	if (mc_verbose) printf("---\n");

	while (cstack)
	{
		n1 = cstack;
		n1->flag = 0;
		cstack = cstack->stack;

		for (edge = n1->bkedges; edge; edge = edge->nextfrom)
		{
			/* tmp1 = (ex p,y: edge->e /\ n1->y)(p'y'->py) */
			Cudd_Ref(tmp0 = Cudd_bddAndAbstract
				(mc_mgr,edge->e,n1->y,mc_cube1));
			Cudd_Ref(tmp1 = Cudd_bddPermute
				(mc_mgr,tmp0,mc_perm1));
			Cudd_RecursiveDeref(mc_mgr,tmp0);

			if (mc_verbose) printf(":::\n");
			add_y_edge(edge->from,tmp1,&cstack);

			if (mc_demand && edge->from == n && n->flag)
			{
				/* ex q,y'': n->y /\ (py=qy'') */
				Cudd_Ref(tmp0 = Cudd_bddAndAbstract
					(mc_mgr,n->y,mc_pyeqv,mc_cube2));
				if (tmp0 == emptyset) continue;
				Cudd_RecursiveDeref(mc_mgr,n->z);
				n->z = tmp0;
				goto cleanup;
			}
		}
	}

	if (!mc_demand)
	{
		/* n->z = ex q,y'': n->y /\ (py=qy'') */
		Cudd_Ref(tmp0 = Cudd_bddAndAbstract
			(mc_mgr,n->y,mc_pyeqv,mc_cube2));
		Cudd_RecursiveDeref(mc_mgr,n->z);
		n->z = tmp0;
	}
	else
	{
		Cudd_RecursiveDeref(mc_mgr,n->z);
		Cudd_Ref(n->z = emptyset);
	}

cleanup:
	for (n1 = snode; n1; n1 = n1->next)
			Cudd_RecursiveDeref(mc_mgr,n1->y);
}
