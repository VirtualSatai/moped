/*****************************************************************************/

#include <stdlib.h>

#include "common.h"
#include "expr.h"
#include "mcheck.h"

identref_t idchain;
const_t constlist, quantlist;
DdNode *exprbdd;

extern prop_t mc_properties;
extern int div_exception;
extern NameTreeList mc_atoms;

DdNode *build_values ()
{
	identref_t tmp;
	DdNode *tmp0, *tmp1, *tmp2;
	DdNode **v;

	Cudd_Ref(tmp0 = fullset);
	for (tmp = idchain; tmp; tmp = tmp->next)
	{
		int i, baseindex, value = tmp->value;

		if (tmp->ident->dim)
		{
			int val;
			div_exception = 0;
			val = etree_eval(tmp->sub);
			if (div_exception || val < tmp->ident->lo
				|| val > tmp->ident->hi)
			{
				Cudd_RecursiveDeref(mc_mgr,tmp0);
				Cudd_Ref(emptyset);
				return emptyset;
			}
			baseindex = tmp->ident->index
				+ (val - tmp->ident->lo) * tmp->ident->type;
		}
		else
			baseindex = tmp->ident->index;

		v = malloc(tmp->ident->type * sizeof(DdNode*));

		for (i = tmp->ident->type-1; i >= 0; i--)
		{
			tmp1 = tmp->context[baseindex + i];
			if (!(value & 1)) tmp1 = Cudd_Not(tmp1);
			v[i] = tmp1;
			value >>= 1;
		}

		Cudd_Ref(tmp1 = Cudd_bddComputeCube(mc_mgr,v,NULL,
				tmp->ident->type));
		free(v);
		Cudd_Ref(tmp2 = Cudd_bddAnd(mc_mgr,tmp0,tmp1));
		Cudd_RecursiveDeref(mc_mgr,tmp0);
		Cudd_RecursiveDeref(mc_mgr,tmp1);
		tmp0 = tmp2;
	}
	return tmp0;
}

void try_all_vars (FormulaTree tree, identref_t idref, identref_t bvar)
{
	if (!idref)
	{
		DdNode *tmp0, *tmp1;
		int val;
		div_exception = 0;
		val = etree_eval(tree);
		if (div_exception) return;
		if (!bvar && !val) return;
		if (bvar && (val < bvar->ident->lo || val > bvar->ident->hi))
			return;

		tmp0 = build_values();
		if (bvar)
		{
			Cudd_Ref(tmp1 = Cudd_bddAnd(mc_mgr,tmp0,
					    bvar->context[bvar->ident->index
						+ val - bvar->ident->lo]));
			Cudd_RecursiveDeref(mc_mgr,tmp0);
			tmp0 = tmp1;
		}
		Cudd_Ref(tmp1 = Cudd_bddOr(mc_mgr,exprbdd,tmp0));
		Cudd_RecursiveDeref(mc_mgr,exprbdd);
		Cudd_RecursiveDeref(mc_mgr,tmp0);
		exprbdd = tmp1;
		return;
	}
	while (idref->value < idref->maxval)
	{
		try_all_vars(tree,idref->next,bvar);
		idref->value++;
	}
	idref->value = 0;
}

identref_t add_to_idchain (identref_t idref)
{
	identref_t tmp;

	for (tmp = idchain; tmp; tmp = tmp->next)
		if (tmp->ident == idref->ident
			&& tmp->context == idref->context)
		{
			free(idref);
			return tmp;
		}

	idref->next = idchain;
	idchain = idref;
	return idref;
}

void delete_idchain ()
{
	while (idchain)
	{
		identref_t tmp = idchain->next;
		free(idchain);
		idchain = tmp;
	}
}

identref_t find_in_block (block_t blk, Name varname, DdNode **context)
{
	ident_t id;
	identref_t idref;

	for (id = blk->idents; id; id = id->next)
		if (id->varname == varname)
		{
			idref = malloc(sizeof(struct identref_element));
			idref->ident = id;
			idref->context = context;
			idref->value = 0;
			idref->maxval = id->type? (1<<id->type) : 2;
			idref->sub = NULL;
			idref->next = NULL;
			return idref;
		}
	return NULL;
}

identref_t find_ident (Name yscope, Name varname,
			DdNode **pcontext, DdNode **ycontext)
{
	NameNode n1;
	identref_t idref;

	if (yscope && ycontext)
	{
		if ((n1 = name_tree_find(mc_localtree,yscope)))
		{
			idref = find_in_block(n1->block,varname,ycontext);
			if (idref) return idref;
		}
	}

	if (!pcontext) return NULL;
	return find_in_block(mc_blocks,varname,pcontext);
}

void build_iexpr (FormulaTree tree)
{
	DdNode *tmp1 = NULL, *tmp2;

	/* equality between variables */
	if (tree->right->token == E_EQ &&
		tree->right->left->token == E_IDENT &&
		tree->right->right->token == E_IDENT)
	{
		identref_t idr1 = tree->right->left->idref;
		identref_t idr2 = tree->right->right->idref;
		ident_t id1 = idr1->ident;
		ident_t id2 = idr2->ident;
		if (!id1->dim && !id2->dim && id1->type == id2->type
			&& id1->lo == id2->lo && id1->hi == id2->hi)
		{
			int i;

			Cudd_Ref(exprbdd = fullset);
			for (i = id1->type-1; i >= 0; i--)
			{
				Cudd_Ref(tmp1 = Cudd_bddXnor(mc_mgr,
					idr1->context[id1->index + i],
					idr2->context[id2->index + i]));
				Cudd_Ref(tmp2
					= Cudd_bddAnd(mc_mgr,exprbdd,tmp1));
				Cudd_RecursiveDeref(mc_mgr,tmp1);
				Cudd_RecursiveDeref(mc_mgr,exprbdd);
				exprbdd = tmp2;
			}

			return;
		}
	}

	/* equality between variables and constants */
	if (tree->right->token == E_EQ &&
		tree->right->left->token == E_IDENT &&
		tree->right->right->token == E_NUMBER)
	{
		identref_t idr1 = tree->right->left->idref;
		int number = (int)(tree->right->right->idref);
		ident_t id1 = idr1->ident;

		if (!id1->dim)
		{
			int i;

			if (number < 0 || number >= idr1->maxval)
			{
				Cudd_Ref(exprbdd = emptyset);
				return;
			}

			Cudd_Ref(exprbdd = fullset);
			for (i = id1->type-1; i >= 0; i--)
			{
				tmp1 = idr1->context[id1->index + i];
				if (!(number & 1)) tmp1 = Cudd_Not(tmp1);
				Cudd_Ref(tmp2
					= Cudd_bddAnd(mc_mgr,exprbdd,tmp1));
				Cudd_RecursiveDeref(mc_mgr,exprbdd);
				exprbdd = tmp2;
				number >>= 1;
			}

			return;
		}
	}
		
	Cudd_Ref(exprbdd = emptyset);
	idchain = (identref_t) tree->left;
	try_all_vars(tree->right,idchain,NULL);
}

DdNode *build_expr (FormulaTree tree)
{
	DdNode* (*fn)(DdManager*,DdNode*,DdNode*) = NULL;
	DdNode *tmp0, *tmp1, *tmp2;
	const_t q;

	switch (tree->token)
	{
	    case E_OR:
		fn = Cudd_bddOr;
	    case E_AND:
		if (!fn) fn = Cudd_bddAnd;
	    case E_EQV:
		if (!fn) fn = Cudd_bddXnor;
	    case E_XOR:
		if (!fn) fn = Cudd_bddXor;
		tmp1 = build_expr(tree->left);
		tmp2 = build_expr(tree->right);
		Cudd_Ref(tmp0 = fn(mc_mgr,tmp1,tmp2));
		Cudd_RecursiveDeref(mc_mgr,tmp1);
		Cudd_RecursiveDeref(mc_mgr,tmp2);
		return tmp0;
	    case E_NOT:
		return Cudd_Not(build_expr(tree->left));
	    case E_FORALL:
	    case E_EXISTS:
		fn = (tree->token == E_FORALL)? Cudd_bddAnd : Cudd_bddOr;
		Cudd_Ref(tmp0 = (tree->token == E_FORALL)? fullset : emptyset);
		q = (const_t)(tree->idref);
		for (q->value = q->lower; q->value <= q->upper; q->value++)
		{
			tmp1 = build_expr(tree->left);
			Cudd_Ref(tmp2 = fn(mc_mgr,tmp0,tmp1));
			Cudd_RecursiveDeref(mc_mgr,tmp0);
			Cudd_RecursiveDeref(mc_mgr,tmp1);
			tmp0 = tmp2;
		}
		return tmp0;
	    case E_BVAR:
		if (!tree->right)
		{
		    Cudd_Ref(tree->idref->context[tree->idref->ident->index]);
		    return tree->idref->context[tree->idref->ident->index];
		}
		idchain = (identref_t) tree->left;
		Cudd_Ref(exprbdd = emptyset);
		try_all_vars(tree->right,idchain,tree->idref);
		return exprbdd;
	    case E_IEXPR:
		build_iexpr(tree);
		return exprbdd;
	    default:
		common_error("unexpected token in build_expr (%i)",tree->token);
		return NULL;
	}
}

void free_expr_tree (FormulaTree tree)
{
	switch (tree->token)
	{
	    case E_OR:
	    case E_AND:
	    case E_EQV:
	    case E_XOR:
		free_expr_tree(tree->left);
		free_expr_tree(tree->right);
		free(tree);
		break;
	    case E_FORALL:
	    case E_EXISTS:
		free(tree->idref);
	    case E_NOT:
		free_expr_tree(tree->left);
		free(tree);
		break;
	    case E_BVAR:
	    case E_IEXPR:
		if (tree->idref)
		    free(tree->idref);
		if (tree->right) ftree_delete(tree->right);
		delete_idchain();
		break;
	    default:
		common_error("unexpected token (%i)", tree->token);
		break;
	}
}

/*****************************************************************************/

DdNode* build_condition (FormulaTree tree, Name state, Name symbol)
{
	DdNode *(*f)(DdManager*,DdNode*,DdNode*) = NULL;
	DdNode *tmp0, *tmp1, *tmp2;
	NameNode n1;
	block_t blk;
	prop_t p;
	NameTreeList atoms;

	switch (tree->token)
	{
	    case F_IDENT:
		Cudd_Ref(fullset);

		/* labels (for boolean programs) */
		if (mc_bp)
		{
			char *dp = strchr(name_cstring(symbol),':');
			if (!dp) return emptyset;
			return strcmp(dp+1,name_cstring(tree->ident))?
				emptyset : fullset;
		}

		/* state or symbol name */
		if (tree->ident == state || tree->ident == symbol)
			return fullset;

		/* atom */
		for (atoms = mc_atoms; atoms; atoms = atoms->next)
			if (tree->ident == atoms->name)
				return name_bal_find(atoms->tree,symbol)?
						fullset : emptyset;
		
		n1 = name_tree_find(mc_localtree,symbol);
		blk = n1? n1->block : mc_blocks;

		/* procedure name */
		if (blk->procname == tree->ident)
			return fullset;

		/* condition on variables */
		for (p = blk->props; p; p = p->next)
			if (p->prop == tree->ident)
			{
				Cudd_Ref(p->cond);
				return p->cond;
			}

		/* all has failed */
		return emptyset;

	    case F_NOT:
		return Cudd_Not(build_condition(tree->left,state,symbol));
	    case F_AND: if (!f) f = Cudd_bddAnd;
	    case F_OR:  if (!f) f = Cudd_bddOr;
		tmp0 = build_condition(tree->left,state,symbol);
		tmp1 = build_condition(tree->right,state,symbol);
		Cudd_Ref(tmp2 = f(mc_mgr,tmp0,tmp1));
		Cudd_RecursiveDeref(mc_mgr,tmp0);
		Cudd_RecursiveDeref(mc_mgr,tmp1);
		return tmp2;
	    case F_TRUE:
		Cudd_Ref(fullset); return fullset;
	    case F_FALSE:
		Cudd_Ref(emptyset); return emptyset;
	    default:
		common_error("unknown token (%i)", tree->token);
		return NULL;
	}
}

/*****************************************************************************/

#define E_NONCONST 0x4321

int interpret_const (FormulaTree tree)
{
	int tmp1, tmp2;
	const_t con;

	switch (tree->token)
	{
	    case E_PLUS:
	    case E_MINUS:
	    case E_MULT:
	    case E_DIV:
	    case E_SHL:
		tmp1 = interpret_const(tree->left);
		tmp2 = interpret_const(tree->right);
		if (tmp1 == E_NONCONST || tmp2 == E_NONCONST)
			return E_NONCONST;
		if (tree->token == E_PLUS) return tmp1 + tmp2;
		if (tree->token == E_MINUS) return tmp1 - tmp2;
		if (tree->token == E_MULT) return tmp1 * tmp2;
		if (tree->token == E_DIV) return tmp1 / tmp2;
		if (tree->token == E_SHL) return tmp1 << tmp2;
		return E_NONCONST;	/* can't happen */

	   case E_IDENT:
		for (con = constlist; con; con = con->next)
			if (con->name == tree->ident) return con->value;
		return E_NONCONST;

	   case E_NUMBER:
		return (int)tree->idref;

	   default:	/* E_QUANT */
		return E_NONCONST;
	}
}

FormulaTree interpret_intterm (FormulaTree, block_t);

FormulaTree interpret_variable (FormulaTree tree, block_t blk, int type)
{
	identref_t idref = NULL;
	FormulaTree tmp1;
	const_t con;

	for (con = constlist; con; con = con->next)
	{
		if (con->name != tree->ident) continue;
		return etree_create(E_NUMBER,(identref_t)con->value,NULL,NULL);
	}

	if (blk != mc_blocks)
		idref = find_in_block(blk,tree->ident,ypvars);
	if (!idref)
		idref = find_in_block(mc_blocks,tree->ident,ppvars);

	if (!idref) return NULL;

	/* incompatible type, invalid/missing subscript */
	if ((!idref->ident->type == type)
                    || (!!idref->ident->dim ^ !!tree->right))
	{
		free(idref); return NULL;
	}

	if (tree->right)
	{
		tmp1 = interpret_intterm(tree->right,blk);
		if (!tmp1) { free(idref); return NULL; }
	}
	else
		tmp1 = NULL;

	return etree_create(E_IDENT,idref,NULL,tmp1);
}

FormulaTree interpret_intterm (FormulaTree tree, block_t blk)
{
	FormulaTree tmp1, tmp2;
	const_t q, nq;

	switch (tree->token)
	{
	    case E_PLUS:
	    case E_MINUS:
	    case E_MULT:
	    case E_DIV:
	    case E_SHL:
		tmp1 = interpret_intterm(tree->left,blk);
		tmp2 = interpret_intterm(tree->right,blk);
		if (!tmp1 || !tmp2)
		{
			if (tmp1) ftree_delete(tmp1);
			if (tmp2) ftree_delete(tmp2);
			return NULL;
		}
		return etree_create(tree->token,0,tmp1,tmp2);

	   case E_IDENT:
		tmp1 = interpret_variable(tree,blk,1);
		if (!tmp1) return NULL;
		if (tmp1->token == E_NUMBER) return tmp1;

		tmp1->token = E_IDENT;
		if (tree->right)
		{
			tmp1->idref->sub = tmp1->right;
			tmp1->right = NULL;
			tmp1->idref->next = idchain;
			idchain = tmp1->idref;
		}
		else
			add_to_idchain(tmp1->idref);

		return tmp1;

	   case E_QUANT:
		q = (const_t) tree->idref;
		for (nq = quantlist; nq; nq = nq->next)
		{
			if (q->name != nq->name) continue;
			return etree_create(E_QUANT,(identref_t)nq,NULL,NULL);
		}
		return NULL;	/* shouldn't happen */

	   case E_NUMBER:
		return etree_create(E_NUMBER,tree->idref,NULL,NULL);

	    default:
		common_error("unexpected token in intterm (%i)", tree->token);
		return NULL;
	}
}

FormulaTree interpret_tree (FormulaTree tree, block_t blk)
{
	FormulaTree tmp1, tmp2;
	const_t q, nq;

	switch (tree->token)
	{
	    case E_OR:
	    case E_AND:
	    case E_EQV:
	    case E_XOR:
		tmp1 = interpret_tree(tree->left,blk);
		tmp2 = interpret_tree(tree->right,blk);
		if (!tmp1 || !tmp2)
		{
			if (tmp1) free_expr_tree(tmp1);
			if (tmp2) free_expr_tree(tmp2);
			return NULL;
		}
		return etree_create(tree->token,0,tmp1,tmp2);

	    case E_NOT:
		tmp1 = interpret_tree(tree->left,blk);
		if (!tmp1) return NULL;
		return etree_create(tree->token,0,tmp1,NULL);

	    case E_FORALL:
	    case E_EXISTS:
		q = (const_t)tree->idref;
                nq = malloc(sizeof(struct const_element));
                nq->name = q->name;

		nq->lower = interpret_const((FormulaTree)q->lower);
		nq->upper = interpret_const((FormulaTree)q->upper);
		if (nq->lower == E_NONCONST || nq->upper == E_NONCONST)
		{
			common_error("quantifier has non-constant limit "
					"in property");
		}

		nq->next = quantlist;
		quantlist = nq;

		tmp1 = interpret_tree(tree->left,blk);
		if (!tmp1)
		{
		    free(nq);
		    tmp2 = NULL;
		}
		else
		    tmp2 = etree_create(tree->token,(identref_t)nq,tmp1,NULL);

		quantlist = quantlist->next;
		return tmp2;

	    case E_IDENT:
		idchain = NULL;
		tmp2 = interpret_variable(tree,blk,0);
		if (!tmp2)
		{
			delete_idchain();
			return NULL;
		}

		tmp2->token = E_BVAR;
		tmp2->left = (FormulaTree)idchain;
		idchain = NULL;
		return tmp2;

	    case E_IEXPR:
		idchain = NULL;
		tmp1 = interpret_intterm(tree->left,blk);
		tmp2 = interpret_intterm(tree->right,blk);
		if (!tmp1 || !tmp2)
		{
			if (tmp1) ftree_delete(tmp1);
			if (tmp2) ftree_delete(tmp2);
			delete_idchain();
			return NULL;
		}
		tmp2 = etree_create(E_IEXPR,0,idchain,
			etree_create(tree->ident,0,tmp1,tmp2));
		idchain = NULL;
		return tmp2;

	    default:
		common_error("unexpected token in tree (%i)", tree->token);
		return NULL;
	}
}

void build_properties (block_t blk)
{
	prop_t p, np;

	blk->props = NULL;
	for (p = mc_properties; p; p = p->next)
	{
		np = malloc(sizeof(struct prop_element));
		np->prop = p->prop;

		np->tree = interpret_tree(p->tree,blk);
		if (np->tree)
		{
			np->cond = build_expr(np->tree);
			free_expr_tree(np->tree);
		}
		else
			Cudd_Ref(np->cond = emptyset);

		np->next = blk->props;
		blk->props = np;
	}
}

/*****************************************************************************/

void define_value (char *s)
{
	const_t con;
	char *c = strchr(s,'=');

	if (!c) common_error("'=' expected in define");
	*c = 0;
	con = malloc(sizeof(struct const_element));
	con->name = name_create(s+1);
	con->value = atoi(c+1);
	con->next = constlist;
	constlist = con;
}
