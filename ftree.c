/* =========================================================================

   Definition der Datenstrukturen und Funktionen
   zur Verwaltung von Transitionen des Buechi-Automaten

   ====================================================================== */

#include <stdio.h>
#include "ftree.h"
#include "common.h"
#include "variables.h"

FormulaTree ftree_create (int token, Name ident,
			   FormulaTree left, FormulaTree right)
{
	FormulaTree ret = common_malloc(sizeof(struct FormulaTreeStruct));

	ret->token = token;
	ret->ident = ident;
	ret->idref = NULL;
	ret->left  = left;
	ret->right = right;
	return ret;
}

FormulaTree ftree_copy (FormulaTree tree)
{
	FormulaTree ret;

	if (!tree) return NULL;
	ret = common_malloc(sizeof(struct FormulaTreeStruct));
	memcpy(ret,tree,sizeof(struct FormulaTreeStruct));
	ret->left  = ftree_copy(tree->left);
	ret->right = ftree_copy(tree->right);
	return ret;
}

void ftree_delete (FormulaTree delete_tree)
{
	if (!delete_tree) return;
	ftree_delete(delete_tree->left);
	ftree_delete(delete_tree->right);
	common_free(delete_tree,sizeof(struct FormulaTreeStruct));
}

FormulaTree etree_create (int token, identref_t idref,
			   void* left, void* right)
{
	FormulaTree ret = common_malloc(sizeof(struct FormulaTreeStruct));

	ret->token = token;
	ret->ident = 0;
	ret->idref = idref;
	ret->left  = (FormulaTree) left;
	ret->right = (FormulaTree) right;
	return ret;
}

/* this is an ugly hack to handle division by zero */
int div_exception;

int etree_eval (FormulaTree tree)
{
	switch (tree->token)
	{
	    case E_NUMBER:
		return (int)(tree->idref);
	    case E_QUANT:
		return ((const_t)(tree->idref))->value;
	    case E_IDENT:
		return tree->idref->value;
	    case E_PLUS:
		return etree_eval(tree->left) + etree_eval(tree->right);
	    case E_MINUS:
		return etree_eval(tree->left) - etree_eval(tree->right);
	    case E_MULT:
		return etree_eval(tree->left) * etree_eval(tree->right);
	    case E_DIV: {
			int divisor = etree_eval(tree->right);
			if (!divisor) { div_exception = 1; return 0; }
			return etree_eval(tree->left) / divisor;
		}
	    case E_SHL:
		return etree_eval(tree->left) << etree_eval(tree->right);
	    case E_LT:
		return etree_eval(tree->left) < etree_eval(tree->right);
	    case E_LE:
		return etree_eval(tree->left) <= etree_eval(tree->right);
	    case E_EQ:
		return etree_eval(tree->left) == etree_eval(tree->right);
	    case E_NE:
		return etree_eval(tree->left) != etree_eval(tree->right);
	    case E_GE:
		return etree_eval(tree->left) >= etree_eval(tree->right);
	    case E_GT:
		return etree_eval(tree->left) > etree_eval(tree->right);
	    default:
		common_error("unexpected token (%i)", tree->token);
		return 0;
	}
}
