#ifndef EXPR_H
#define EXPR_H

#include "name.h"
#include "bdd.h"
#include "variables.h"
#include "ftree.h"

extern identref_t idchain;
extern const_t constlist, quantlist;
extern NameTree mc_localtree;

extern identref_t add_to_idchain (identref_t);
extern identref_t find_ident (Name, Name, DdNode**, DdNode**);
extern DdNode *build_expr (FormulaTree);
extern void free_expr_tree (FormulaTree);
extern DdNode* build_condition (FormulaTree,Name,Name);
extern void build_properties (block_t);
extern void define_value (char*);

#endif
