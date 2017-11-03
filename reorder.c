#include <stdlib.h>
#include <string.h>
#include "variables.h"
#include "bpstruc.h"
#include "bdd.h"
#include "common.h"

void (*mc_reorderproc)();
block_t mc_maxblock;
extern int mc_stats, mc_bp;
extern int mc_poststar, mc_restrict;
extern bp_tree_t bp_indextree;

/***************************************************************************/

void reorder_varbitcopy ()			/* -m0 */
	/* var (global,local) */
	/* msb ... lsb */
	/* p',p,q resp. y,y'',y',y''' */
{
	int *shuffle = malloc((GLOBALS + LOCALS + 1) * sizeof(int));
	int i, nl = (mc_poststar && !mc_restrict)? 4 : 3;

	if (mc_stats) printf("Initial ordering is gl/var/bit/copy.\n\n");

	shuffle[0] = bvars - bddvars;
	for (i = 0; i < global_vars; i++)
		shuffle[i*3+1] = ppvars - pvars + i,	/* p', p, q */
		shuffle[i*3+2] = i,
		shuffle[i*3+3] = qvars - pvars + i;
	for (i = 0; i < local_vars; i++)		/* y, y'', y', y''' */
	{
		shuffle[GLOBALS + 1 + i*nl] = yppvars - bddvars + i,
		shuffle[GLOBALS + 3 + i*nl] = ypvars - bddvars + i,
		shuffle[GLOBALS + 2 + i*nl] = yvars - bddvars + i;
		if (nl == 4)
			shuffle[GLOBALS + nl + i*nl] = ypppvars - bddvars + i;
	}

	mc_shuffle = shuffle;
}

/***************************************************************************/

void reorder_bitvarcopy ()			/* -m1 */
	/* msb..lsb */
	/* var (global,local) */
	/* p',p,q resp. y,y'',y',y''' */
{
	int *shuffle = malloc((GLOBALS + LOCALS + 1) * sizeof(int));
	ident_t id;
	int base, i, j, m, n;

	if (mc_stats) printf("Initial ordering is bit/var/copy.\n\n");

	shuffle[0] = bvars - bddvars;
	for (i = 1, j = 0; i != GLOBALS + LOCALS + 1; j++)
	{
	    for (id = mc_blocks->idents; id; id = id->next)
	    {
		if (id->type <= j && (id->type || j)) continue;
		n = id->dim? id->dim : 1;
		base = id->index;
		for (m = 0; m < n; m++)
		{
		    shuffle[i++] = pvars - bddvars + base + j,
		    shuffle[i++] = qvars - bddvars + base + j,
		    shuffle[i++] = ppvars - bddvars + base + j;
		    base += id->type? id->type : 1;
		}
	    }
	    if (!mc_maxblock) continue;
	    for (id = mc_maxblock->idents; id; id = id->next)
	    {
		if (id->type <= j && (id->type || j)) continue;
		n = id->dim? id->dim : 1;
		base = id->index;
		for (m = 0; m < n; m++)
		{
		    shuffle[i++] = yvars - bddvars + base + j,
		    shuffle[i++] = yppvars - bddvars + base + j,
		    shuffle[i++] = ypvars - bddvars + base + j;
		    if (mc_poststar && !mc_restrict)
			shuffle[i++] = ypppvars - bddvars + base + j;
		    base += id->type? id->type : 1;
		}
	    }
	}

	mc_shuffle = shuffle;
}

/***************************************************************************/

void reorder_varcopybit ()			/* -m2 */
	/* var (global,local) */
	/* p,q,p' resp. y,y'',y',y''' */
	/* msb..lsb */
{
	int *shuffle = malloc((GLOBALS + LOCALS + 1) * sizeof(int));
	ident_t id;
	int base, i = 1, j, k, m, n;

	if (mc_stats) printf("Initial ordering is var/copy/bit.\n\n");

	shuffle[0] = bvars - bddvars;
	for (id = mc_blocks->idents; id; id = id->next)
	{
	    k = id->type? id->type : 1;
	    n = id->dim? id->dim : 1;
	    base = id->index;
	    for (m = 0; m < n; m++)
	    {
		for (j = 0; j < k; j++)
		    shuffle[i++] = pvars - bddvars + base + j;
		for (j = 0; j < k; j++)
		    shuffle[i++] = qvars - bddvars + base + j;
		for (j = 0; j < k; j++)
		    shuffle[i++] = ppvars - bddvars + base + j;
		base += k;
	    }
	}

	if (mc_maxblock) for (id = mc_maxblock->idents; id; id = id->next)
	{
	    k = id->type? id->type : 1;
	    n = id->dim? id->dim : 1;
	    base = id->index;
	    for (m = 0; m < n; m++)
	    {
		for (j = 0; j < k; j++)
		    shuffle[i++] = yvars - bddvars + id->index + j;
		for (j = 0; j < k; j++)
		    shuffle[i++] = yppvars - bddvars + id->index + j;
		for (j = 0; j < k; j++)
		    shuffle[i++] = ypvars - bddvars + id->index + j;
		if (mc_poststar && !mc_restrict)
		    for (j = 0; j < k; j++)
			shuffle[i++] = ypppvars - bddvars + id->index + j;
		base += k;
	    }
	}

	mc_shuffle = shuffle;
}

/***************************************************************************/

void reorder_lgbitvarcopy ()			/* -m3 */
	/* local: msb..lsb, var, y',y'',y,y'''
	   global: msb..lsb, var, p',p,q
	*/
{
	int *shuffle = malloc((GLOBALS + LOCALS + 1) * sizeof(int));
	ident_t id;
	int base, i = 1, j, m, n;

	if (mc_stats) printf("Initial ordering is lg/bit/var/copy.\n\n");

	shuffle[0] = bvars - bddvars;
	if (mc_maxblock)
	  for (j = 0; i != LOCALS + 1; j++)
	  {
	    for (id = mc_maxblock->idents; id; id = id->next)
	    {
		if (id->type <= j && (id->type || j)) continue;
		n = id->dim? id->dim : 1;
		base = id->index + (n-1)*(id->type? id->type : 1);
		for (m = 0; m < n; m++)
		{
		    shuffle[i++] = ypvars - bddvars + base + j,
		    shuffle[i++] = yppvars - bddvars + base + j,
		    shuffle[i++] = yvars - bddvars + base + j;
		    if (mc_poststar && !mc_restrict)
			shuffle[i++] = ypppvars - bddvars + base + j;
		    base -= id->type? id->type : 1;
		}
	    }
	  }

	for (j = 0; i != GLOBALS + LOCALS + 1; j++)
	{
	    for (id = mc_blocks->idents; id; id = id->next)
	    {
		if (id->type <= j && (id->type || j)) continue;
		n = id->dim? id->dim : 1;
		base = id->index + (n-1)*(id->type? id->type : 1);
		for (m = 0; m < n; m++)
		{
		    shuffle[i++] = ppvars - bddvars + base + j,
		    shuffle[i++] = pvars - bddvars + base + j,
		    shuffle[i++] = qvars - bddvars + base + j;
		    base -= id->type? id->type : 1;
		}
	    }
	}

	mc_shuffle = shuffle;
}

/***************************************************************************/

void reorder_lgvarbitcopy ()			/* -m4 */
	/* var (local,global) */
	/* msb ... lsb */
	/* p',p,q resp. y,y'',y',y''' */
{
	int *shuffle = malloc((GLOBALS + LOCALS + 1) * sizeof(int));
	int i, nl = (mc_poststar && !mc_restrict)? 4 : 3;

	if (mc_stats) printf("Initial ordering is lg/var/bit/copy.\n\n");

	shuffle[0] = bvars - bddvars;
	for (i = 0; i < local_vars; i++)		/* y', y'', y, y''' */
	{
		shuffle[1 + i*nl] = ypvars - bddvars + i,
		shuffle[2 + i*nl] = yppvars - bddvars + i,
		shuffle[3 + i*nl] = yvars - bddvars + i;
		if (nl == 4) shuffle[nl + i*nl] = ypppvars - bddvars + i;
	}
	for (i = 0; i < global_vars; i++)
		shuffle[LOCALS + i*3+1] = ppvars - pvars + i,	/* p', p, q */
		shuffle[LOCALS + i*3+2] = i,
		shuffle[LOCALS + i*3+3] = qvars - pvars + i;

	mc_shuffle = shuffle;
}

/***************************************************************************/

void reorder_lgmixed ()				/* -m5 */
	/* local: msb..lsb, var, y',y'',y,y'''
	   global: p',p,q, var, msb..lsb
	*/
{
	int *shuffle = malloc((GLOBALS + LOCALS + 1) * sizeof(int));
	ident_t id;
	int base, i = 1, j, m, n;

	if (mc_stats) printf("Initial ordering is lg/mixed.\n\n");

	shuffle[0] = bvars - bddvars;
	if (mc_maxblock)
	  for (j = 0; i != LOCALS + 1; j++)
	  {
	    for (id = mc_maxblock->idents; id; id = id->next)
	    {
		if (id->type <= j && (id->type || j)) continue;
		n = id->dim? id->dim : 1;
		base = id->index;
		for (m = 0; m < n; m++)
		{
		    shuffle[i++] = ypvars - bddvars + base + j,
		    shuffle[i++] = yppvars - bddvars + base + j,
		    shuffle[i++] = yvars - bddvars + base + j;
		    if (mc_poststar && !mc_restrict)
			shuffle[i++] = ypppvars - bddvars + base + j;
		    base += id->type? id->type : 1;
		}
	    }
	  }

	for (i = 0; i < global_vars; i++)
		shuffle[LOCALS + i*3+1] = ppvars - pvars + i,	/* p', p, q */
		shuffle[LOCALS + i*3+2] = i,
		shuffle[LOCALS + i*3+3] = qvars - pvars + i;

	mc_shuffle = shuffle;
}

/***************************************************************************/

void reorder_byfunction ()				/* -m6 */
	/* local: msb..lsb, var, y',y'',y,y'''
	   global: p',p,q, var, msb..lsb
	*/
{

#define add_local(var) \
		    shuffle[i++] = ypvars - bddvars + var->index, \
		    shuffle[i++] = yppvars - bddvars + var->index, \
		    shuffle[i++] = yvars - bddvars + var->index; \
		    if (mc_poststar && !mc_restrict) \
				shuffle[i++] = ypppvars - bddvars + var->index; \
			var->varname = -var->varname  - 1;
			

	int *shuffle = malloc((GLOBALS + LOCALS + 1) * sizeof(int));
	bp_ident_t var;
	int i = 1, j, m;
	Name nm;

	if (mc_stats) printf("Initial ordering is by functionality.\n\n");

	shuffle[0] = bvars - bddvars;
	for (j = 0; j < bp_numglobals; j++)
		shuffle[i++] = ppvars - pvars + j,	/* p', p, q */
		shuffle[i++] = j,
		shuffle[i++] = qvars - pvars + j;

	for (j = 1, m = 0; m != i; j++)
	{
		char tmp[32];

		m = i;
		sprintf(tmp,"*param%d",j);
		nm = name_create(tmp);

		for (var = bp_locids; var; var = var->next)
		{
			if (var->varname != nm) continue;
			add_local(var);
		}

		sprintf(tmp,"prm%d",j);
		nm = name_create(tmp);

		for (var = bp_locids; var; var = var->next)
		{
			if (var->varname != nm) continue;
			add_local(var);
		}
	}

	for (var = bp_locids; var; var = var->next)
	{
		if (var->varname < 0) continue;
		if (!strncmp(name_cstring(var->varname),"funRet",6)) continue;
		if (!strncmp(name_cstring(var->varname),"ret",3)) continue;
		add_local(var);
	}

	for (j = bp_numglobals; j < bp_maxrets; j++)
	{
		char tmp[32];

		shuffle[i++] = ppvars - pvars + j,	/* p', p, q */
		shuffle[i++] = j,
		shuffle[i++] = qvars - pvars + j;

		sprintf(tmp,"funRet%d",j-bp_numglobals+1);
		nm = name_create(tmp);

		for (var = bp_locids; var; var = var->next)
		{
			if (var->varname != nm) continue;
			add_local(var);
		}

		sprintf(tmp,"ret%d",j-bp_numglobals+1);
		nm = name_create(tmp);

		for (var = bp_locids; var; var = var->next)
		{
			if (var->varname != nm) continue;
			add_local(var);
		}
	}

	for (var = bp_locids; var; var = var->next)
	{
		if (var->varname < 0) continue;
		add_local(var);
	}

	if (i != GLOBALS+LOCALS+1)
		common_error("didn't find all the vars??");

	for (var = bp_locids; var; var = var->next)
		var->varname = -var->varname - 1;

	mc_shuffle = shuffle;
}

/***************************************************************************/

void print_shuffle ()
{
	DdNode *node, *b_shuffle;
	ident_t id;
	block_t block;
	int i, k, offset, pos = 0;
	char *app;

	int *shuffle = malloc((GLOBALS + LOCALS + 1) * sizeof(int));
	for (i = 0; i < GLOBALS + LOCALS + 1; i++)	/* identity */
		shuffle[i] = i;
    Cudd_Ref(b_shuffle = Cudd_IndicesToCube
                        (mc_mgr, shuffle, GLOBALS + LOCALS + 1));
	free(shuffle);

	printf("\n*** Current variable ordering:\n");
	for (node = b_shuffle; node->index != 0xffff; node = Cudd_T(node))
	{
		int index = mc_shuffle[node->index];

	    printf("pos #%u: ",pos++);
	    if (index < yvars-pvars)
	    {
			offset = index % global_vars;
			block = mc_bp? (block_t) bp_allglobids : mc_blocks;
			if (index < qvars-pvars) app = ".p";
			else if (index < ppvars-pvars) app = ".q";
			else app = ".p'";
		}
		else if (index < bvars-pvars)
		{
			offset = (index - GLOBALS) % local_vars;
			block = mc_bp? (block_t) bp_locids : mc_maxblock;
			if (index < ypvars-pvars) app = ".y";
			else if (index < yppvars-pvars) app = ".y'";
			else if (index >= ypppvars-pvars
				&& mc_poststar && !mc_restrict)
				app = ".y'''";
			else app = ".y''";
		}
		else
		{
			printf("b\n");
			continue;
	    }

	    if (mc_bp)
	    {
			bp_ident_t var;
			for (var = (bp_ident_t) block; var; var = var->next)
			{
				if (offset != var->index) continue;
				printf("%s%s\n",name_cstring(var->varname),app);
				break;
			}
			continue;
	    }
	    for (id = block->idents; id; id = id->next)
	    {
			k = (id->type? id->type : 1) * (id->dim? id->dim : 1);
			if (offset >= id->index + k) continue;
			offset -= id->index;
			printf("%s",name_cstring(id->varname));
			if (id->dim)
			{
				int t = id->type? id->type : 1;
				printf("[%u]",(offset/t) + id->lo);
				offset = offset % t;
			}
			printf("%s",app);
			if (id->type) printf(" bit %u",id->type - 1 - offset);
			printf("\n");
			break;
	    }
	}
	printf("\n");

	Cudd_RecursiveDeref(mc_mgr,b_shuffle);
}
