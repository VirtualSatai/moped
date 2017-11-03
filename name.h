/* =========================================================================

   Deklaration der Datenstrukturen und Funktionen
   zur Verwaltung von Namen

   ========================================================================= */

#ifndef NAME_H
#define NAME_H

#include "bdd.h"

extern char **name_globals_array;

/* --------------------------   Datatypes   -------------------------------- */

#define NAME_HASH_MIN 1024
#define NAME_GLOBALS_DELTA 1024

typedef struct NameListElementStruct *NameSet;
typedef struct NameListElementStruct *NameListElement;
typedef struct NameStackElementStruct *NameStack;
typedef struct NameStackElementStruct *NameStackElement;
typedef struct NameTreeStruct *NameTree;
typedef struct NameNodeStruct *NameNode;
typedef struct NameTreeListStruct *NameTreeList;
typedef struct NameBalTreeStruct *NameBalTree;
typedef int Name;

struct NameListElementStruct
{
	int name;
	unsigned long hash;
	NameListElement next;
};

struct NameTreeListStruct
{
	int name;
	NameBalTree tree;
	NameTreeList next;
};

struct NameBalTreeStruct
{
	int name;
	signed char bal;
	NameBalTree left, right;
};

struct NameStackElementStruct
{
	int name;
	DdNode *bdd;
	NameStackElement next;
};

struct NameTreeStruct
{
	int used;
	int alloc;
	NameNode *data;
};

struct NameNodeStruct
{
	int name;
	int refname;
	struct block_element *block;
};

/* --------------------------   Functions   -------------------------------- */

#define name_cstring(name) (name_globals_array[name])
#define name_hashvalue(name, table_size) ((ulong) ((name)*(name)) % table_size)
#define name_compare(name1, name2) (((int) name2)-((int) name1))
#define name_set_empty() NULL
#define name_stack_empty() NULL
#define name_stack_isempty(stack) (!(stack))

int name_create(char *name);

int name_set_insert (NameSet*,int);
int name_set_find (NameSet,int);
void name_set_delete (NameSet*);

void name_stack_push (NameStack*,int,DdNode*);
void name_stack_delete (NameStack*);

signed char name_bal_insert (NameBalTree*,Name);
int name_bal_find (NameBalTree,Name);

NameNode name_tree_mknode (Name,Name,struct block_element*);
void name_tree_insert (NameTree*,NameNode);
NameNode name_tree_find (NameTree,Name);
void name_tree_delete (NameTree*);

void name_global_empty ();
void name_global_delete ();

#endif
