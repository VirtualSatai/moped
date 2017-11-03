/****************************************************************************/
/* bdd.c								    */
/*									    */
/* Initialises the BDD manager.						    */
/*									    */
/* Stefan Schwoon, February 2000					    */
/****************************************************************************/

#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include "bdd.h"
#include "reorder.h"
#include "bpstruc.h"
#include "common.h"
#include "sort.h"

extern int mc_bp;

DdManager *mc_mgr;
DdNode **bddvars;
DdNode **pvars, **qvars, **ppvars;
DdNode **yvars, **ypvars, **yppvars, **ypppvars;
DdNode **bvars;
DdNode *mc_cube1, *mc_cube2, *mc_cube3;
DdNode *mc_cube4, *mc_cube5, *mc_cube6;
DdNode *mc_cube7, *mc_cube8, *mc_cube9;
DdNode *mc_cube10, *fullset, *emptyset;
DdNode *mc_pyeqv, *mc_qyeqv, *mc_yyeqv;

int *mc_perm1, *mc_perm2, *mc_perm3, *mc_perm4;
int *mc_perm5, *mc_perm6, *mc_perm7, *mc_perm8;
int *mc_perm9, *mc_perm10, *mc_perm11, *mc_perm12;
int *mc_perm13, *mc_perm14;

int global_vars, local_vars;
int *global_var, *local_var;
int *mc_shuffle, *mc_rev_shuffle;

char mc_autoreorder = 0;

unsigned char *bddval;
char *bdd_data[8];

block_t bblock;
bp_ident_t bp_bblock;
extern char mc_maxreorder;
extern NameTree mc_localtree;

extern int mc_poststar;
extern int mc_restrict;

void print_bddvars (block_t blk, int offset, char *template)
{
	ident_t id;
	int i, j, k, m, n, base, bit, mult, val, second;

	if (!blk) return;

	if (mc_bp)
	{
	    bp_ident_t var;

	    for (var = (bp_ident_t) blk; var; var = var->next)
	    {
		if ((unsigned char)bddval[offset+var->index] == 0xff) continue;
		common_addbuf(*common_strbuf? " & " : "(");
		if (!bddval[offset+var->index]) common_addbuf("!");
		common_addbuf(template,name_cstring(var->varname));
	    }
	    return;
	}

	for (id = blk->idents; id; id = id->next)
	{
	  n = id->dim? id->dim : 1;
	  for (m = 0, base = id->index; m < n;
		m++, base += id->type? id->type : 1)
	  {
	    if (id->type)	/* integer */
	    {
		mult = val = second = 0;
		for (i = 0; i < id->type; i++)
		{
		    if ((unsigned char)bddval[offset + base + i] == 0xff)
			mult++;
		    else
			val++;
		}
		if (!val) continue;
		common_addbuf(*common_strbuf? " & " : "(");
		common_addbuf(template,name_cstring(id->varname));
		if (id->dim) common_addbuf("[%u]",m+id->lo);
		common_addbuf(mult? " in {" : "=");
		for (k = 0; k < (1<<id->type); k++)
		{
		    j = k;
		    for (i = id->type-1; i >= 0; i--, j>>=1)
		    {
			bit = (unsigned char)bddval[offset + base + i];
			if (bit == 0xff) continue;
			if (bit == 1 && !(j & 1)) break;
			if (bit == 0 && (j & 1)) break;
		    }
		    if (i >= 0) continue;
		    common_addbuf(second++? ",%u" : "%u", k);
		}
		if (mult) common_addbuf("}");
	    }
	    else		/* boolean */
	    {
		if ((unsigned char)bddval[offset + base] == 0xff) continue;
		common_addbuf(*common_strbuf? " & " : "(");
		if (!bddval[offset + base]) common_addbuf("!");
		common_addbuf(template,name_cstring(id->varname));
		if (id->dim) common_addbuf("[%u]",m+id->lo);
	    }
	  }
	}
}

void recurse_bdd (DdNode *bdd, int inv, int *col, char **dsc,
			block_t blk1, block_t blk2, block_t blk3, block_t blk4)
{
	inv ^= Cudd_IsComplement(bdd);
	bdd = Cudd_Regular(bdd);

	if (bdd->index == 0xffff)
	{
		block_t gblock = mc_blocks;

		if (!(inv ^ !!bdd->type.value)) return;

		common_strbuf_new();

		if (mc_bp) gblock = (block_t) bp_globids;
		print_bddvars(gblock,0,dsc[0]);			/* p   */
		print_bddvars(gblock,qvars-pvars,dsc[1]);	/* q   */
		print_bddvars(gblock,ppvars-pvars,dsc[2]);	/* p'  */
		print_bddvars(blk1,yvars-pvars,dsc[3]);		/* y   */
		print_bddvars(blk2,ypvars-pvars,dsc[4]);	/* y'  */
		print_bddvars(blk3,yppvars-pvars,dsc[5]);	/* y'' */
		if (mc_poststar && !mc_restrict)
			print_bddvars(blk4,ypppvars-pvars,dsc[6]); /* y''' */
		gblock = mc_bp? (block_t) bp_bblock : bblock;
		print_bddvars(gblock,bvars-pvars,dsc[7]);	/* b   */
		common_addbuf(*common_strbuf? ")" : " ");

		if (*col > 1 && *col+strlen(common_strbuf) > 77)
			{ printf("\n"); *col = 1; }
		printf(*col? " v " : " ");
		*col += (*col? 3 : 1);
		while (strlen(common_strbuf) > 76)
		{
			char *j = common_strbuf+76;
			while (*j != '&') j--;
			if (j == common_strbuf)
			{
				j = strchr(common_strbuf+1,'&');
				if (!j) break;
			}
			j[-1] = '\n'; *j = 0; printf(common_strbuf);
			*j = '&'; memcpy(common_strbuf,j,strlen(j)+1);
			*col = 5; printf("    ");
		}
		printf(common_strbuf); *col += strlen(common_strbuf);
	}
	else
	{
		bddval[mc_shuffle[bdd->index]] = 0;
		recurse_bdd(Cudd_E(bdd),inv,col,dsc,blk1,blk2,blk3,blk4);
		bddval[mc_shuffle[bdd->index]] = 1;
		recurse_bdd(Cudd_T(bdd),inv,col,dsc,blk1,blk2,blk3,blk4);
		bddval[mc_shuffle[bdd->index]] = 0xff;
	}
}

char *fatrans_set[] = { "%s", "%s'", "ERR",
			"%s", "ERR", "ERR", "ERR", "b" };

char *rule_set[] = {  "%s'", "ERR", "%s",
			"%s'", "%s", "%s''", "ERR", "b" };

char *pre_set_all[] = {  "%s", "ERR", "%s''",
			"%s'", "ERR", "ERR", "ERR", "ERR" };

char *pre_set_front[] = {  "%s", "ERR", "ERR",
			"%s", "ERR", "ERR", "ERR", "ERR" };

char *post_set_init[] = {  "ERR", "%s''", "%s",
			"ERR", "%s'", "ERR", "%s''", "ERR" };

char *post_set_mid[] = {  "%s", "%s''", "ERR",
			"%s", "%s'", "ERR", "%s''", "ERR" };

char *post_set_front[] = {  "ERR", "ERR", "%s",
			"ERR", "%s", "ERR", "ERR", "ERR" };

char *post_trans_set[] = {  "ERR", "ERR", "%s",
			"ERR", "%s", "ERR", "ERR", "ERR" };

block_t lookup_bp (Name local)
{
	if (!local) return NULL;
	return (block_t)
		(((bp_fun_t)bp_find_var(bp_labeltree,local,-2))->locals);
}

block_t lookup_pds (Name local)
{
	NameNode n;

	if (!local) return NULL;
	n = name_tree_find(mc_localtree,local);
	return n? n->block : NULL;
}

void print_bdd (DdNode *bdd, char **dsc, int local1, int local2,
					 int local3, int local4)
{
	int col = 0;

	block_t blk1 = (mc_bp? lookup_bp : lookup_pds)(local1);
	block_t blk2 = (mc_bp? lookup_bp : lookup_pds)(local2);
	block_t blk3 = (mc_bp? lookup_bp : lookup_pds)(local3);
	block_t blk4 = (mc_bp? lookup_bp : lookup_pds)(local4);

	common_strbuf_new();
	memset(bddval,0xff,(GLOBALS + LOCALS + 1) * sizeof(char));
	recurse_bdd(bdd,0,&col,dsc,blk1,blk2,blk3,blk4);

	printf(*common_strbuf? "\n" : " false\n");
}

/***************************************************************************/

void bdd_correct_perm (int *perm, int *tmp)
{
	int i;

	for (i = 0; i < GLOBALS + LOCALS + 1; i++)
		tmp[mc_rev_shuffle[i]] = mc_rev_shuffle[perm[i]];
	memcpy(perm,tmp,(GLOBALS + LOCALS + 1) * sizeof(int));
}

DdNode* bdd_get_cube(int *vars, int num)
{
	DdNode *result;
	int i;

	for (i = 0; i < num; i++) vars[i] = mc_rev_shuffle[vars[i]];
	sort_int(vars,0,num-1);
	Cudd_Ref(result = Cudd_IndicesToCube(mc_mgr,vars,num));
	free(vars);
	return result;
}

/***************************************************************************/

void init_cudd ()
{
	DdNode *tmp0, *tmp1;
	DdNode **svx, **svy;
	int *cubev1, *cubev2, *cubev3;
	int *cubev4, *cubev5, *cubev6;
	int *cubev7, *cubev8, *cubev9;
	int *cubev10;
	int i, *mc_ptmp, *mc_pyperm;
	int extravars = mc_poststar && !mc_restrict;

	/* create p,q,p', y,y',y'',y''', b */
	bddvars = malloc((global_vars*3 + local_vars*(3+extravars) + 1)
				* sizeof(DdNode*));
	pvars = bddvars; qvars = pvars + global_vars;
	ppvars = qvars + global_vars; yvars = ppvars + global_vars;
	ypvars = yvars + local_vars; yppvars = ypvars + local_vars;
	ypppvars = extravars? yppvars + local_vars : yppvars;
	bvars = ypppvars + local_vars;

	mc_reorderproc();	/* choose variable ordering */
	mc_rev_shuffle = malloc((GLOBALS + LOCALS + 1) * sizeof(int));
	for (i = 0; i < GLOBALS + LOCALS + 1; i++)
		mc_rev_shuffle[mc_shuffle[i]] = i;

	mc_mgr = Cudd_Init(GLOBALS + LOCALS + 1,0,CUDD_UNIQUE_SLOTS,CUDD_CACHE_SLOTS,0);
	if (mc_autoreorder) Cudd_AutodynEnable(mc_mgr,CUDD_REORDER_SAME);

	for (i = 0; i < GLOBALS + LOCALS + 1; i++)
		bddvars[mc_shuffle[i]] = Cudd_bddIthVar(mc_mgr,i);

	fullset = Cudd_ReadOne(mc_mgr);
	emptyset = Cudd_Not(fullset);

	bddval = malloc((global_vars*3 + local_vars*(3+extravars) + 1)
				* sizeof(char));

	/* create permutations:
		mc_perm1  = (p' -> p,  y'  -> y  )
		mc_perm2  = (q  -> p,  y'' -> y  )
		mc_perm3  = (p  -> q,  y   -> y'')
		mc_perm4  = (p' -> q)
		mc_perm5  = (p' -> p,  y'  -> y,   p -> q)
		mc_perm6  = (p  -> p', y   -> y' )
		mc_perm7  = (q  -> p')
		mc_perm8  = (p  -> p', y   -> y'')
		mc_perm9  = (p' -> p,  y'' -> y  )
		mc_perm10 = (y''-> y')
		mc_perm11 = (p  -> p', y'''-> y,   q -> p)
		mc_perm12 = (p  -> p', y   -> y',  p'-> p, y' -> y)
		mc_perm13 = (p  -> q,  y   -> y''')
		mc_perm14 = (y' -> y'')
	*/
	mc_perm1  = malloc((GLOBALS + LOCALS + 1) * sizeof(int));
	mc_perm2  = malloc((GLOBALS + LOCALS + 1) * sizeof(int));
	mc_perm3  = malloc((GLOBALS + LOCALS + 1) * sizeof(int));
	mc_perm4  = malloc((GLOBALS + LOCALS + 1) * sizeof(int));
	mc_perm5  = malloc((GLOBALS + LOCALS + 1) * sizeof(int));
	mc_perm6  = malloc((GLOBALS + LOCALS + 1) * sizeof(int));
	mc_perm7  = malloc((GLOBALS + LOCALS + 1) * sizeof(int));
	mc_perm8  = malloc((GLOBALS + LOCALS + 1) * sizeof(int));
	mc_perm9  = malloc((GLOBALS + LOCALS + 1) * sizeof(int));
	mc_perm10 = malloc((GLOBALS + LOCALS + 1) * sizeof(int));
	mc_perm11 = malloc((GLOBALS + LOCALS + 1) * sizeof(int));
	mc_perm12 = malloc((GLOBALS + LOCALS + 1) * sizeof(int));
	mc_perm13 = malloc((GLOBALS + LOCALS + 1) * sizeof(int));
	mc_perm14 = malloc((GLOBALS + LOCALS + 1) * sizeof(int));
	mc_ptmp   = malloc((GLOBALS + LOCALS + 1) * sizeof(int));

	for (i = 0; i < GLOBALS + LOCALS + 1; i++)	/* identity */
		mc_perm1[i] = mc_perm2[i] = mc_perm3[i]
		  = mc_perm4[i] = mc_perm5[i] = mc_perm6[i]
		  = mc_perm7[i] = mc_perm8[i] = mc_perm9[i]
		  = mc_perm10[i] = mc_perm11[i] = mc_perm12[i]
		  = mc_perm13[i] = mc_perm14[i] = i;

	for (i = 0; i < global_vars; i++)
	{
		mc_perm1[i + global_vars*2] = i;		/* p' -> p  */
		mc_perm2[i + global_vars] = i;			/* q  -> p  */
		mc_perm3[i] = i + global_vars;			/* p  -> q  */
		mc_perm4[i + global_vars*2] = i + global_vars;	/* p' -> q  */
		mc_perm5[i + global_vars*2] = i;		/* p' -> p  */
		mc_perm6[i] = i + global_vars*2;		/* p  -> p' */
		mc_perm8[i] = i + global_vars*2;		/* p  -> p' */

		mc_perm5[i] = i + global_vars;			/* p  -> q  */
		mc_perm7[i + global_vars] = i + global_vars*2;	/* q  -> p' */
		mc_perm9[i + global_vars*2] = i;		/* p' -> p  */
		mc_perm11[i] = i + global_vars*2;		/* p  -> p' */
		mc_perm11[i + global_vars] = i;			/* q  -> p  */
		mc_perm12[i] = i + global_vars*2;		/* p  -> p' */
		mc_perm12[i + global_vars*2] = i;		/* p' -> p  */
		mc_perm13[i] = i + global_vars;			/* p  -> q  */
	}

	for (i = GLOBALS; i < GLOBALS + local_vars; i++)
	{
		mc_perm1[i + local_vars] = i;			/* y'  -> y   */
		mc_perm2[i + local_vars*2] = i;			/* y'' -> y   */
		mc_perm3[i] = i + local_vars*2;			/* y   -> y'' */
		mc_perm5[i + local_vars] = i;			/* y'  -> y   */
		mc_perm6[i] = i + local_vars;			/* y   -> y'  */
		mc_perm8[i] = i + local_vars*2;			/* y   -> y'' */
		mc_perm9[i + local_vars*2] = i;			/* y'' -> y   */
		mc_perm10[i + local_vars*2] = i + local_vars;	/* y'' -> y'  */
		mc_perm11[i+local_vars*(2+extravars)] = i;	/* y'''-> y   */
		mc_perm12[i] = i + local_vars;			/* y   -> y'  */
		mc_perm12[i + local_vars] = i;			/* y'  -> y   */
		mc_perm13[i] = i+local_vars*(2+extravars);	/* y   -> y'''*/
		mc_perm14[i + local_vars] = i + local_vars*2;	/* y'  -> y'' */
	}

	bdd_correct_perm(mc_perm1,mc_ptmp);
	bdd_correct_perm(mc_perm2,mc_ptmp);
	bdd_correct_perm(mc_perm3,mc_ptmp);
	bdd_correct_perm(mc_perm4,mc_ptmp);
	bdd_correct_perm(mc_perm5,mc_ptmp);
	bdd_correct_perm(mc_perm6,mc_ptmp);
	bdd_correct_perm(mc_perm7,mc_ptmp);
	bdd_correct_perm(mc_perm8,mc_ptmp);
	bdd_correct_perm(mc_perm9,mc_ptmp);
	bdd_correct_perm(mc_perm10,mc_ptmp);
	bdd_correct_perm(mc_perm11,mc_ptmp);
	bdd_correct_perm(mc_perm12,mc_ptmp);
	bdd_correct_perm(mc_perm13,mc_ptmp);
	bdd_correct_perm(mc_perm14,mc_ptmp);
	free(mc_ptmp);

	svx = malloc((global_vars+local_vars) * sizeof(DdNode*));
	svy = malloc((global_vars+local_vars) * sizeof(DdNode*));
	for (i = 0; i < global_vars; i++)	/* p'->q */
		svx[i] = ppvars[i], svy[i] = qvars[i];
	for (i = 0; i < local_vars; i++)	/* y'->y'' */
		svx[i+global_vars] = ypvars[i], svy[i+global_vars] = yppvars[i];
	Cudd_SetVarMap(mc_mgr,svx,svy,global_vars+local_vars);
	free(svx); free(svy);

    /* create cubes:
            cube1 = (p,y,b)	 cube2 = (q,y'')  cube3 = (p',y')
			cube4 = (q,y)	 cube5 = (p,q)	  cube6 = (y'')
			cube7 = (q,y',y''')               cube8 = (q,y''')
			cube9 = (p')	 cube10 = (p)						*/
    cubev1 = malloc((global_vars + local_vars + 1) * sizeof(int));
    cubev2 = malloc((global_vars + local_vars) * sizeof(int));
    cubev3 = malloc((global_vars + local_vars) * sizeof(int));
    cubev4 = malloc((global_vars + local_vars) * sizeof(int));
    cubev5 = malloc((global_vars + global_vars) * sizeof(int));
    cubev6 = malloc(local_vars * sizeof(int));
    cubev7 = malloc((global_vars + local_vars*2) * sizeof(int));
    cubev8 = malloc((global_vars + local_vars) * sizeof(int));
    cubev9 = malloc(global_vars * sizeof(int));
    cubev10 = malloc(global_vars * sizeof(int));

    for (i = 0; i < global_vars; i++)
    {
		cubev1[i] = i;								/* p  */
		cubev2[i] = i + global_vars;				/* q  */
		cubev3[i] = i + global_vars*2;				/* p' */
		cubev4[i] = i + global_vars;				/* q  */
		cubev5[i] = i;								/* p  */
		cubev5[i+global_vars] = i + global_vars;	/* q  */
		cubev7[i] = i + global_vars;				/* q  */
		cubev8[i] = i + global_vars;				/* q  */
		cubev9[i] = i + global_vars*2;				/* p' */
		cubev10[i] = i;								/* p  */
	}

	for (i = 0; i < local_vars; i++)
	{
		cubev1[i + global_vars] = i + GLOBALS;			/* y    */
		cubev2[i + global_vars]
			= i + GLOBALS + local_vars*2;				/* y''  */
		cubev3[i + global_vars]
			= i + GLOBALS + local_vars;					/* y'   */
		cubev4[i + global_vars] = i + GLOBALS;			/* y    */
		cubev6[i] = i + GLOBALS + local_vars*2;			/* y''  */
		cubev7[i + global_vars]
			= i + GLOBALS + local_vars;					/* y'   */
		cubev7[i + global_vars + local_vars]
			= i + GLOBALS + local_vars*(2+extravars);	/* y''' */
		cubev8[i + global_vars]
			= i + GLOBALS + local_vars*(2+extravars);	/* y''' */
	}

	cubev1[global_vars + local_vars] = bvars - bddvars;     /* b */

	mc_cube1 = bdd_get_cube(cubev1,global_vars + local_vars + 1);
	mc_cube2 = bdd_get_cube(cubev2,global_vars + local_vars);
	mc_cube3 = bdd_get_cube(cubev3,global_vars + local_vars);
	mc_cube4 = bdd_get_cube(cubev4,global_vars + local_vars);
	mc_cube5 = bdd_get_cube(cubev5,global_vars + global_vars);
	mc_cube6 = bdd_get_cube(cubev6,local_vars);
	if (mc_poststar) 
		mc_cube7 = bdd_get_cube(cubev7,global_vars + local_vars*2);
	if (mc_poststar)
		mc_cube8 = bdd_get_cube(cubev8,global_vars + local_vars);
	if (mc_poststar)
		mc_cube9 = bdd_get_cube(cubev9,global_vars);
	if (mc_poststar)
		mc_cube10 = bdd_get_cube(cubev10,global_vars);

	mc_pyperm = malloc((global_vars + local_vars) * sizeof(int));
	for (i = 0; i < global_vars; i++)
		mc_pyperm[i] = mc_rev_shuffle[i];
	for (i = 0; i < local_vars; i++)
		mc_pyperm[global_vars + i] = mc_rev_shuffle[GLOBALS + i];
	sort_int(mc_pyperm,0,global_vars + local_vars - 1);

	/* compute bdd for (p /\ y <=> q /\ y'') */
	mc_pyeqv = Cudd_ReadOne(mc_mgr);
	for (i = global_vars + local_vars - 1; i >= 0; i--)
	{
		int j = mc_shuffle[mc_pyperm[i]];
		if (j < GLOBALS)
			Cudd_Ref(tmp0 = Cudd_bddXnor(mc_mgr,pvars[j],qvars[j]));
		else
			Cudd_Ref(tmp0 = Cudd_bddXnor(mc_mgr,yvars[j-GLOBALS],yppvars[j-GLOBALS]));
		Cudd_Ref(tmp1 = Cudd_bddAnd(mc_mgr,mc_pyeqv,tmp0));
		Cudd_RecursiveDeref(mc_mgr,tmp0);
		Cudd_RecursiveDeref(mc_mgr,mc_pyeqv);
		mc_pyeqv = tmp1;
	}

	if (mc_poststar)
	{
		/* compute bdd for (p' /\ y' <=> q /\ y'''/y'') */
		mc_qyeqv = Cudd_ReadOne(mc_mgr);
		for (i = global_vars + local_vars - 1; i >= 0; i--)
		{
			int j = mc_shuffle[mc_pyperm[i]];
			if (j < GLOBALS)
				Cudd_Ref(tmp0 = Cudd_bddXnor(mc_mgr,ppvars[j],qvars[j]));
			else
				Cudd_Ref(tmp0 = Cudd_bddXnor(mc_mgr,ypvars[j-GLOBALS],ypppvars[j-GLOBALS]));
			Cudd_Ref(tmp1 = Cudd_bddAnd(mc_mgr,mc_qyeqv,tmp0));
			Cudd_RecursiveDeref(mc_mgr,tmp0);
			Cudd_RecursiveDeref(mc_mgr,mc_qyeqv);
			mc_qyeqv = tmp1;
		}

		/* compute bdd for (y' <=> y'') */
		mc_yyeqv = Cudd_ReadOne(mc_mgr);
		for (i = global_vars + local_vars - 1; i >= 0; i--)
		{
			int j = mc_shuffle[mc_pyperm[i]];
			if (j < GLOBALS) continue;
			else Cudd_Ref(tmp0 = Cudd_bddXnor(mc_mgr,ypvars[j-GLOBALS],yppvars[j-GLOBALS]));
			Cudd_Ref(tmp1 = Cudd_bddAnd(mc_mgr,mc_yyeqv,tmp0));
			Cudd_RecursiveDeref(mc_mgr,tmp0);
			Cudd_RecursiveDeref(mc_mgr,mc_yyeqv);
			mc_yyeqv = tmp1;
		}
	}

	free(mc_pyperm);

	/* create a block_t for boolean flags */
	bblock = malloc(sizeof(struct block_element));
	bblock->names = NULL;
	bblock->idents = malloc(sizeof(struct ident_element));
	bblock->idents->varname = name_create("b");
	bblock->idents->type = 0;
	bblock->idents->dim = bblock->idents->lo = bblock->idents->hi = 0;
	bblock->idents->index = 0;
	bblock->idents->next = NULL;
	bblock->next = NULL;

	bp_bblock = alloc_bp_ident();
	bp_bblock->varname = name_create("b");
	bp_bblock->index = 0;
	bp_bblock->next = NULL;
}

#include "cuddInt.h"

void check_refs (char *s)
{
	DdNode **nodelist;
	DdManager *unique = mc_mgr;
	DdNode *node, *sentinel = &(unique->sentinel);
	int i, j, slots, deleted, totalDeleted = 0;

	printf("%s\n",s);
	for (i = 0; i < unique->size; i++)
	{
		if (unique->subtables[i].dead == 0) continue;
		nodelist = unique->subtables[i].nodelist;

		deleted = 0;
		slots = unique->subtables[i].slots;
		for (j = 0; j < slots; j++)
		{
			node = nodelist[j];
			while (node != sentinel)
			{
				if (node->ref == 0) deleted++;
				node = node->next;
			}
		}
		if ((unsigned) deleted != unique->subtables[i].dead)
		{
			printf("disorder in subtable %i (%u,%u)\n", i,
				(unsigned) deleted, unique->subtables[i].dead);
			exit(1);
		}
		totalDeleted += deleted;
	}

	if (unique->constants.dead != 0)
	{
		nodelist = unique->constants.nodelist;
		deleted = 0;
		slots = unique->constants.slots;
		for (j = 0; j < slots; j++)
		{
			node = nodelist[j];
			while (node != NULL)
			{
				if (node->ref == 0) deleted++;
				node = node->next;
			}
		}
		if ((unsigned) deleted != unique->constants.dead)
		{
			printf("disorder in constants (%u,%u)\n",
				(unsigned) deleted, unique->constants.dead);
			exit(1);
		}
		totalDeleted += deleted;
	}
	if ((unsigned) totalDeleted != unique->dead)
	{
		printf("disorder in table (%u,%u)\n",
				(unsigned) totalDeleted, unique->dead);
		exit(1);
	}

	printf("----\n");
}
