/* =========================================================================

   Deklaration der Datenstrukturen und Funktionen
   zur Verwaltung von Formelbaeumen

   ====================================================================== */

#ifndef FTREE_H
#define FTREE_H

#include "name.h"
#include "variables.h"

typedef struct FormulaTreeStruct* FormulaTree;

struct FormulaTreeStruct
{
	char   token;
	Name   ident;
	identref_t idref;
	FormulaTree left, right;
};

enum {	F_FALSE, F_TRUE,
	F_NOT, F_AND, F_OR, F_IMP, F_EQV,
	F_F, F_G, F_U, F_V, F_X,
	F_IDENT };

FormulaTree ftree_create(int,Name,FormulaTree,FormulaTree);
FormulaTree ftree_copy(FormulaTree);
void ftree_delete(FormulaTree delete_tree);

enum {	E_NUMBER, E_IDENT, E_BVAR, E_IEXPR,
	E_PLUS, E_MINUS, E_MULT, E_DIV, E_SHL,
	E_LT, E_LE, E_EQ, E_NE, E_GE, E_GT,
	E_OR, E_AND, E_EQV, E_XOR, E_NOT,
	E_FORALL, E_EXISTS, E_QUANT };

FormulaTree etree_create(int,identref_t,void*,void*);
int etree_eval(FormulaTree);

#endif
