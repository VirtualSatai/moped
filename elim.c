#include "cycle.h"
#include "variables.h"
#include "common.h"

#include <cuddInt.h>

#define crp(index) Cudd_ReadPerm(mc_mgr,index)
/*#define crp(index) (mc_mgr->perm[index])*/

extern int bp_maxrets, bp_maxlocs;

int flipvar[2];

int find_flip (DdNode *bdd, int index0, int index1, int level, int inv)
{
	int g, idx = -1;
	inv ^= Cudd_IsComplement(bdd);
	bdd = Cudd_Regular(bdd);

	if (bdd->index == 0xffff || crp(bdd->index) > level)
	{
		if (bdd->index == 0xffff
			&& !(inv ^ !!bdd->type.value)) return 0;
		if (flipvar[0] == flipvar[1])
			return (flipvar[0] == 0xff)? 3 : 0;
		return (flipvar[0] == 0)? 1
		     : (flipvar[0] == 1)? 2
		     : (flipvar[1] == 0)? 2 : 1;
	}

 	if (bdd->index == index0) idx = 0;
	if (bdd->index == index1) idx = 1;

	if (idx >= 0) flipvar[idx] = 0;
	g = find_flip(Cudd_E(bdd),index0,index1,level,inv);
	if (g != 3)
	{
		if (idx >= 0) flipvar[idx] = 1;
		g = g | find_flip(Cudd_T(bdd),index0,index1,level,inv);
	}
	if (idx >= 0) flipvar[idx] = 0xff;
	return g;
}

char eliminate_var (int base, int dim, int type,
		   CNode snode, DdNode **base1, DdNode **base2)
{
	DdNode *eq, *tmp0;
	CNode n1;
	CEdge edge;
	int k, m, r, index1, index2, lv, lv1, lv2;
	char retval = 0;

	for (m = 0; m < dim; m++)
	{
	    for (k = 0; k < type; k++)
	    {
		index1 = mc_rev_shuffle[(base1-bddvars) + base + k];
		index2 = mc_rev_shuffle[(base2-bddvars) + base + k];
		lv1 = crp(index1);
		lv2 = crp(index2);
		lv = (lv1 > lv2)? lv1 : lv2;
		flipvar[0] = flipvar[1] = 0xff;

		r = 0;
		for (n1 = snode; n1; n1 = n1->next)
		{
			for (edge = n1->fwedges; edge; edge = edge->nextto)
			{
				r |= find_flip(edge->e,index1,index2,lv,0);
				if (r == 3) goto raus;
			}
		}

		raus:
		if (r == 3) break;
		if (r == 0) continue;

		Cudd_Ref(eq = Cudd_bddXnor(mc_mgr,bddvars[mc_shuffle[index1]],
						  bddvars[mc_shuffle[index2]]));

		for (n1 = snode; n1; n1 = n1->next)
		{
			for (edge = n1->fwedges; edge; edge = edge->nextto)
			{
				Cudd_Ref(tmp0 = Cudd_bddAnd(mc_mgr,edge->e,eq));
				Cudd_RecursiveDeref(mc_mgr,edge->e);
				edge->e = tmp0;
			}
		}

		retval = 1;
		Cudd_RecursiveDeref(mc_mgr,eq);
	    }
	    base += type;
	}

	return retval;
}

char eliminate_flips (CNode snode, block_t blk, DdNode **base1, DdNode **base2)
{
	ident_t id;
	char retval = 0;

	for (id = blk->idents; id; id = id->next)
	    if (!id->dim) retval |=
		eliminate_var(id->index, id->dim? id->dim : 1,
			id->type? id->type : 1, snode, base1, base2);
	return retval;
}

char eliminate_bvars (CNode snode, int num, DdNode **base1, DdNode **base2)
{
	int i;
	char retval = 0;

	for (i = 0; i < num; i++)
		retval |= eliminate_var(i, 1, 1, snode, base1, base2);
	return retval;
}

block_t find_block_for_gamma (Name gamma)
{
	block_t blk;

	for (blk = mc_blocks->next; blk; blk = blk->next)
		if (name_set_find(blk->names,gamma)) break;
	return blk;
}

void eliminate_stuff (CNode snode)
{
	block_t blk;
	CNode n1;
	char retval = 1;

	if (mc_verbose > 1) printf("eliminate flips\n");

	while (retval--)
	{
		if (mc_bp)
		{
		    retval |= eliminate_bvars(snode,bp_maxlocs,yvars,ypvars);
		    retval |= eliminate_bvars(snode,bp_maxrets,pvars,ppvars);
		    return;
		}

		/* fixme: if blocks different, look for same names */
		blk = find_block_for_gamma(snode->head->name);
		for (n1 = snode->next; n1; n1 = n1->next)
		    if (find_block_for_gamma(n1->head->name) != blk) blk = NULL;
		if (blk) retval |= eliminate_flips(snode,blk,yvars,ypvars);
		retval |= eliminate_flips(snode,mc_blocks,pvars,ppvars);
	}
}
