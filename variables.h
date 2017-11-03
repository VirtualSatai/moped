/* =========================================================================

   Global/local variables

   ====================================================================== */


#ifndef VARIABLES_H
#define VARIABLES_H

#include "name.h"

typedef struct block_element *block_t;
typedef struct ident_element *ident_t;
typedef struct identref_element *identref_t;
typedef struct const_element *const_t;
typedef struct prop_element *prop_t;

struct prop_element
{
	Name prop;
	struct FormulaTreeStruct* tree;
	DdNode *cond;
	prop_t next;
};

struct block_element
{
	Name procname;
	NameSet names;
	ident_t idents;
	block_t next;
	prop_t props;
};

struct ident_element
{
	Name varname;
	char type;
	int dim, lo, hi;
	int index;
	ident_t next;
};

struct identref_element
{
	ident_t ident;
	DdNode **context;
	int value;
	int maxval;
	struct FormulaTreeStruct* sub;
	identref_t next;
};

struct const_element {
	Name name;
	int value;
	int lower;
	int upper;
	const_t next;
};

extern block_t mc_blocks;

#endif
