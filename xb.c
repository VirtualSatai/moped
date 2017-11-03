#include "mcheck.h"
#include "cycle.h"
#include "common.h"

/*****************************************************************************/

/* z contains result; x contains current subgraph */

/* remove states without predecessors in x; w and y are free for use */
void xb_cut_fmdpred (CNode snode)
{
	CNode n1;
	CEdge edge;
	DdNode *tmp0, *tmp1, *tmp2;
	char converged = 0;

	while (!converged)
	{
	    for (n1 = snode; n1; n1 = n1->next)
		Cudd_Ref(n1->w = emptyset);

	    for (n1 = snode; n1; n1 = n1->next)
	    {
		/* tmp0 = x(py->p'y') */
		Cudd_Ref(tmp0 = Cudd_bddPermute(mc_mgr,n1->x,mc_perm6));

		for (edge = n1->fwedges; edge; edge = edge->nextto)
		{
		    /* to->w \/= ex p'y': tmp0 /\ edge->e */
		    Cudd_Ref(tmp1 = Cudd_bddAndAbstract
			(mc_mgr,edge->e,tmp0,mc_cube3));
		    Cudd_Ref(tmp2 = Cudd_bddOr(mc_mgr,edge->to->w,tmp1));
		    Cudd_RecursiveDeref(mc_mgr,tmp1);
		    Cudd_RecursiveDeref(mc_mgr,edge->to->w);
		    edge->to->w = tmp2;
		}

		Cudd_RecursiveDeref(mc_mgr,tmp0);
	    }

	    converged = 1;
	    for (n1 = snode; n1; n1 = n1->next)
	    {
		/* x /\= w */
		Cudd_Ref(tmp0 = Cudd_bddAnd(mc_mgr,n1->x,n1->w));
		if (tmp0 != n1->x) converged = 0;
		Cudd_RecursiveDeref(mc_mgr,n1->x);
		Cudd_RecursiveDeref(mc_mgr,n1->w);
		n1->x = tmp0;
	    }
	}
}

/* remove states without successors in x; w and y are free for use */
void xb_cut_fmdsucc (CNode snode)
{
	CNode n1;
	CEdge edge;
	DdNode *tmp0, *tmp1;
	char converged = 0;

	while (!converged)
	{
	    for (n1 = snode; n1; n1 = n1->next)
		Cudd_Ref(n1->w = emptyset);

	    for (n1 = snode; n1; n1 = n1->next)
		for (edge = n1->bkedges; edge; edge = edge->nextfrom)
		{
		    /* from->w \/= ex py: edge->e /\ x */
		    Cudd_Ref(tmp0 = Cudd_bddAndAbstract
			(mc_mgr,edge->e,n1->x,mc_cube1));
		    Cudd_Ref(tmp1 = Cudd_bddOr(mc_mgr,edge->from->w,tmp0));
		    Cudd_RecursiveDeref(mc_mgr,tmp0);
		    Cudd_RecursiveDeref(mc_mgr,edge->from->w);
		    edge->from->w = tmp1;
		}

	    converged = 1;
	    for (n1 = snode; n1; n1 = n1->next)
	    {
		/* x /\= w(p'y'->py) */
		Cudd_Ref(tmp0 = Cudd_bddPermute(mc_mgr,n1->w,mc_perm1));
		Cudd_RecursiveDeref(mc_mgr,n1->w);
		Cudd_Ref(tmp1 = Cudd_bddAnd(mc_mgr,n1->x,tmp0));
		if (tmp1 != n1->x) converged = 0;
		Cudd_RecursiveDeref(mc_mgr,tmp0);
		Cudd_RecursiveDeref(mc_mgr,n1->x);
		n1->x = tmp1;
	    }
	}
}

/* restrict search to x, write result to y, then to w */
void xb_bksearch (CNode snode, CNode n1, DdNode *v)
{
	CNode cstack;
	CEdge edge;
	DdNode *tmp0, *tmp1;

	Cudd_Ref(v);
	init_y_stack(snode,&cstack);
	add_y_edge(n1,v,&cstack);

	while (cstack)
	{
		n1 = cstack;
		n1->flag = 0;
		cstack = cstack->next;

		for (edge = n1->bkedges; edge; edge = edge->nextfrom)
		{
			/* y \/= x /\ (ex p,y: edge->e /\ y)(p'->p,y'->y) */
			Cudd_Ref(tmp0 = Cudd_bddAndAbstract
				(mc_mgr,edge->e,n1->y,mc_cube1));
			Cudd_Ref(tmp1 = Cudd_bddPermute(mc_mgr,tmp0,mc_perm1));
			Cudd_RecursiveDeref(mc_mgr,tmp0);
			Cudd_Ref(tmp0 = Cudd_bddAnd(mc_mgr,tmp1,edge->from->x));
			Cudd_RecursiveDeref(mc_mgr,tmp1);

			add_y_edge(edge->from,tmp0,&cstack);
		}
	}

	for (n1 = snode; n1; n1 = n1->next) n1->w = n1->y;
}

/* restrict search to w, write result to y */
void xb_fwsearch (CNode snode, CNode n1, DdNode *v)
{
	CNode cstack;
	CEdge edge;
	DdNode *tmp0, *tmp1;

	Cudd_Ref(v);
	init_y_stack(snode,&cstack);
	add_y_edge(n1,v,&cstack);

	while (cstack)
	{
		n1 = cstack;
		n1->flag = 0;
		cstack = cstack->next;

		for (edge = n1->fwedges; edge; edge = edge->nextto)
		{
			/* y \/= w /\ ex p'y': edge->e /\ y(py->p'y') */
			Cudd_Ref(tmp0 = Cudd_bddPermute(mc_mgr,n1->y,mc_perm6));
			Cudd_Ref(tmp1 = Cudd_bddAndAbstract
				(mc_mgr,edge->e,tmp0,mc_cube3));
			Cudd_RecursiveDeref(mc_mgr,tmp0);
			Cudd_Ref(tmp0 = Cudd_bddAnd(mc_mgr,tmp1,edge->to->w));
			Cudd_RecursiveDeref(mc_mgr,tmp1);

			add_y_edge(edge->to,tmp0,&cstack);
		}
	}
}

/* check for 1-edge in y */
char xb_check (CNode snode)
{
	CNode n1;
	CEdge edge;
	DdNode *tmp0, *tmp1;

	for (n1 = snode; n1; n1 = n1->next)
	    for (edge = n1->fwedges; edge; edge = edge->nextto)
	    {
		if (!edge->b) continue;

		/* edge->e /\ from->y(py->p'y') /\ to->y != emptyset? */
		Cudd_Ref(tmp0 = Cudd_bddPermute(mc_mgr,n1->y,mc_perm6));
		Cudd_Ref(tmp1 = Cudd_bddAnd(mc_mgr,edge->e,tmp0));
		Cudd_RecursiveDeref(mc_mgr,tmp0);
		Cudd_Ref(tmp0 = Cudd_bddAnd(mc_mgr,tmp1,edge->to->y));
		Cudd_RecursiveDeref(mc_mgr,tmp1);
		Cudd_RecursiveDeref(mc_mgr,tmp0);
		if (tmp0 != emptyset) goto found;
	    }

	return 0;

found:	/* z \/= y */
	for (n1 = snode; n1; n1 = n1->next)
	{
		Cudd_Ref(tmp0 = Cudd_bddOr(mc_mgr,n1->z,n1->y));
		Cudd_RecursiveDeref(mc_mgr,n1->z);
		n1->z = tmp0;
	}
	
	return 1;
}

CNode xb_clone (CNode snode)
{
	CNode tnode;

	if (!snode) return NULL;

	tnode = create_cnode();
	memcpy(tnode,snode,sizeof(struct CNodeStruct));
	tnode->next = xb_clone(snode->next);
	return tnode;
}

char xb_decomp_main (CNode);

/* clone; set x = w\y; do an eg on x and recurse */
char xb_recur (CNode snode)
{
	CNode tnode, n1;
	char retval;

	/* set x = (w \ y) on clone, free w,y in original */
	tnode = xb_clone(snode);
	for (n1 = tnode; n1; n1 = n1->next)
	{
		Cudd_Ref(n1->x = Cudd_bddAnd(mc_mgr,n1->w,Cudd_Not(n1->y)));
		Cudd_RecursiveDeref(mc_mgr,n1->y);
		Cudd_RecursiveDeref(mc_mgr,n1->w);
	}

	xb_cut_fmdsucc(tnode);	/* do an eg on x in tnode */

	retval = xb_decomp_main(tnode);

	/* transfer z to snode and release memory */
	while (tnode)
	{
		tnode = (n1 = tnode)->next;
		Cudd_RecursiveDeref(mc_mgr,n1->x);
		snode->z = n1->z;	/* we only ever have one ref to z */
		snode = snode->next;
		free(n1);
	}
	return retval;
}

/* x contains nodes of current subgraph */
char xb_decomp_main (CNode snode)
{
	CNode n1, n2;
	CEdge edge;
	DdNode *tmp0, *v;
	char retval = 0;

	for (n1 = snode; n1; n1 = n1->next)
	{
	    /* v = findone[py](x) */
	    for (edge = n1->bkedges; edge; edge = edge->nextfrom)
	    {
		/* find targets of 1-edges in x */
		if (!edge->b) continue;

		/* tmp0 = ex p'y': edge->e /\ x */
		Cudd_Ref(tmp0 = Cudd_bddAndAbstract
				(mc_mgr,edge->e,n1->x,mc_cube3));
		if (tmp0 == emptyset)
		{
			Cudd_RecursiveDeref(mc_mgr,tmp0);
			continue;
		}

		Cudd_Ref(v = find_one(n1->x,0)); /* pick a node v */
		xb_bksearch(snode,n1,v);	 /* w contains B(v) */
		xb_fwsearch(snode,n1,v);	 /* y contains F(v) /\ B(v) */
		Cudd_RecursiveDeref(mc_mgr,v);

		retval |= xb_check(snode);	/* check if y has 1-edge */
		if (retval && mc_poststar && mc_demand) return 1;

		/* x /\= !w */			/* remove B(v) from x */
		for (n2 = snode; n2; n2 = n2->next)
		{
		    Cudd_Ref(tmp0 = Cudd_bddAnd(mc_mgr,n1->x,Cudd_Not(n1->w)));
		    Cudd_RecursiveDeref(mc_mgr,n1->x);
		    n1->x = tmp0;
		}

		retval |= xb_recur(snode);	/* check on B(v) \ F(v) */
		if (retval && mc_poststar && mc_demand) return 1;

		xb_cut_fmdpred(snode);		/* do an eh on x */
	    }
	}

	return retval;
}

char xb_decomp (CNode snode)
{
	CNode n1;

	/* cut fmd pred/succ states from the whole set, result goes to x */
	for (n1 = snode; n1; n1 = n1->next) Cudd_Ref(n1->z = emptyset);
	for (n1 = snode; n1; n1 = n1->next) Cudd_Ref(n1->x = fullset);
	xb_cut_fmdsucc(snode);
	xb_cut_fmdpred(snode);

	xb_decomp_main(snode);
	for (n1 = snode; n1; n1 = n1->next) Cudd_RecursiveDeref(mc_mgr,n1->x);

	/* check if repeating head was found */
	for (n1 = snode; n1; n1 = n1->next)
		if (n1->z != emptyset) return 1;
	
	return 0;
}
