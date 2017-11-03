/* =========================================================================

   Functions shared by fwtrace.c and bktrace.c

   ====================================================================== */

#include <stdlib.h>
#include <string.h>
#include "mcheck.h"
#include "sort.h"
#include "bpstruc.h"

DdNode ***fovars[][8] =
      { { &pvars, &yvars, NULL, NULL, NULL, NULL, NULL, NULL },
	{ &pvars, &yvars, &qvars, NULL, NULL, NULL, NULL, NULL },
	{ &pvars, &yvars, &qvars, &yppvars, NULL, NULL, NULL, NULL },
	{ &pvars, &yvars, &ppvars, &yppvars, &qvars, NULL, NULL, NULL },
	{ &ppvars, &ypvars, &qvars, &ypppvars, NULL, NULL, NULL, NULL },
	{ &pvars, &yvars, &ypvars, &qvars, &ypppvars, NULL, NULL, NULL },
	{ &ppvars, &ypvars, &pvars, &yvars, &yppvars, &qvars, &ypppvars, NULL}};

int fologlo[] = { 2, 2, 10, 10, 10, 22, 90 };
int **foperm;

void find_one_init ()
{
	bp_fun_t fun;
	int *v = malloc((GLOBALS + LOCALS + 1) * sizeof(int));
	int useq, i, j, numvars;

	foperm = malloc(6 * sizeof(int*));

	for (useq = 0; useq < 6; useq++)
	{
		numvars = 0;
		for (i = 0; fovars[useq][i]; i++)
		{
			j = (fologlo[useq] & (1 << i))? local_vars : global_vars;
			while (j-- > 0)
				v[numvars + j] = (*fovars[useq][i])[j]->index;
			numvars += (fologlo[useq] & (1 << i))? local_vars : global_vars;
		}

		sort_int(v,0,numvars-1);
		foperm[useq] = malloc((GLOBALS + LOCALS + 1) * sizeof(int));
		memset(foperm[useq],0xff,(GLOBALS + LOCALS + 1) * sizeof(int));
		for (i = 0; i < numvars; i++)
			foperm[useq][v[i]] = i;
	}

	free(v);

	if (mc_bp)
		for (fun = bp_functions; fun; fun = fun->next)
			if (fun->funnode->dfsnum) bp_make_tracemasks(fun);
}

DdNode* find_one(DdNode *bdd, int useq)
{
	DdNode *tb, *cube;
	DdNode **v = malloc((GLOBALS+LOCALS) * sizeof(DdNode*));
	int i, branch, inv = 0, numvars = 0, j;

	for (i = 0; fovars[useq][i]; i++)
	{
		j = (fologlo[useq] & (1 << i))? local_vars : global_vars;
		while (j-- > 0)
		{
			DdNode *var = (*fovars[useq][i])[j];
			v[foperm[useq][var->index]] = Cudd_Not(var);
		}
		numvars += (fologlo[useq] & (1 << i))? local_vars : global_vars;
	}
		
	while (Cudd_Regular(bdd)->index != 0xffff)
	{
		inv = inv ^ Cudd_IsComplement(bdd);
		bdd = Cudd_Regular(bdd);
		tb = Cudd_Regular(Cudd_T(bdd));
		branch = (tb->index != 0xffff ||
		   (!!tb->type.value ^ inv ^ Cudd_IsComplement(Cudd_T(bdd))));
		if (branch)
		{
			int index = foperm[useq][bdd->index];
			if (index != -1) v[index] = bddvars[mc_shuffle[bdd->index]];

		}
		bdd = branch? Cudd_T(bdd) : Cudd_E(bdd);
	}

	cube = Cudd_bddComputeCube(mc_mgr,v,NULL,numvars);
	free(v);
	return cube;
}

int trace_findloop (Path *p, Head start, DdNode *sb, int b,
		    Path (*stepfun)(Path,Rule,DdNode*))
{
	DdNode *tmp0, *tmp1, *tmp2;
	Rule r;
	int c;

	/* tmp1 = (sb /\ b) \ start->rel */
	Cudd_Ref(tmp0 = Cudd_bddAnd(mc_mgr,sb,b? *bvars : Cudd_Not(*bvars)));
	Cudd_Ref(tmp1 = Cudd_bddAnd(mc_mgr,tmp0,Cudd_Not(start->rel)));
	Cudd_RecursiveDeref(mc_mgr,tmp0);
	if (tmp1 == emptyset) return 0;

	/* start->rel \/= tmp1 */
	Cudd_Ref(tmp0 = Cudd_bddOr(mc_mgr,start->rel,tmp1));
	Cudd_RecursiveDeref(mc_mgr,start->rel);
	start->rel = tmp0;

	if (start->dfsnum == -1 && b)	/* loop found */
	{
		Cudd_Ref(tmp0 = Cudd_bddAnd(mc_mgr,start->trans,tmp1));
		if (tmp0 != emptyset)
		{
			Cudd_RecursiveDeref(mc_mgr,tmp0);
			Cudd_RecursiveDeref(mc_mgr,tmp1);
			return 1;
		}
	}

	for (r = start->rules; r; r = r->next)
	{
		if (r->head->comp != start->comp) continue;

		/* tmp2 = (ex p,y,b: tmp1 /\ r->vars)(p'->p,y'->y) */
		Cudd_Ref(tmp0
			= Cudd_bddAndAbstract(mc_mgr,tmp1,r->vars,mc_cube1));
		Cudd_Ref(tmp2 = Cudd_bddPermute(mc_mgr,tmp0,mc_perm1));
		Cudd_RecursiveDeref(mc_mgr,tmp0);

		c = trace_findloop(p, r->head, tmp2, b | r->b, stepfun);
		Cudd_RecursiveDeref(mc_mgr,tmp2);
		if (!c) continue;

		*p = stepfun(*p,r,sb);

		Cudd_RecursiveDeref(mc_mgr,tmp1);
		return 1;
	}

	Cudd_RecursiveDeref(mc_mgr,tmp1);
	return 0;
}
