/* =========================================================================

   Deklaration der Datenstrukturen und Funktionen
   zur Verwaltung von Transitionen

   ====================================================================== */

#ifndef HEAD_H
#define HEAD_H

#define HEAD_HASH_MIN 1024

/* --------------------------   Data types   -------------------------------- */

typedef struct HeadStruct* Head;
typedef struct RuleStruct* Rule;
typedef struct HeadTableStruct HeadTable;

#include "pds.h"
#include "bdd.h"
#include "cycle.h"

struct HeadStruct
{
	Name state;
	Name name;
	unsigned long hash;

	Rule rules;
	Rule fwd;
	Head stack;
	Head list;
	Head vstack;
	Head next;

	DdNode *trans;
	DdNode *rel;

	PDSTransition post;

	CNode cnode;

	int dfsnum, lowpt, comp;
};

struct HeadTableStruct
{
	Head *data;
	Head list;
	long size;
	long mask;
	long fill;
};

struct RuleStruct
{			/* corresponds to a rule headfwd -> head */
	int b, new;
	Head head;
	Head headfwd;
	Name tail;
	PDSTransition origin;
	Name midstate;	/* used for new rules in post* method */
	DdNode *vars;
	Rule next;	/* backward */
	Rule fwdnext;	/* forward */
	int prio;
};

/* --------------------------   Functions   --------------------------------- */

Head head_create (Name, Name);
void head_delete (Head);
int  head_compare (Head, Head);

Head head_list_insert (Head*, Head, int*);
void head_add_rule (Head, Head, Name, int, int, PDSTransition, Name, DdNode*);

HeadTable head_table_empty ();
void head_table_delete (HeadTable*);
Head head_table_insert (HeadTable*, Head);
Head head_find (HeadTable, Name, Name);

#endif
