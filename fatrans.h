/* =========================================================================

   Deklaration der Datenstrukturen und Funktionen
   zur Verwaltung von Transitionen

   ====================================================================== */

#ifndef FATRANS_H
#define FATRANS_H

#include "name.h"
#include "pds.h"
#include "bdd.h"

#define FAT_HASH_MIN 1024
#define FAT_USE_STACK 1
#define FAT_USE_LIST  2
#define FAT_LIST_MARK 4

#define FF_THEAD 1
#define FF_DUMB 2

/* --------------------------   Datatypes   --------------------------------- */

typedef struct FATransitionStruct *FATransition;
typedef struct FATransitionStruct *FATransList;
typedef struct FATransTableStruct  FATransTable;
typedef struct OriginListElement  *OriginList;

struct FATransitionStruct
{
	Name from_state;
	Name name;
	Name to_state;
  
	char b, f;
	DdNode *trans, *rel;
	OriginList origin;
  
	unsigned long hash;
	int prio;
	FATransList stack;
	FATransList list;
	FATransition next;
};

struct FATransTableStruct
{
	FATransList *data;
	FATransition stack;
	FATransition list;
	FATransition *lastptr;
	long size;
	long mask;
	long fill;
	int usestack;
};

struct OriginListElement
{
	PDSTransition pt;
	DdNode *bdd;
	int n;
	OriginList next;
	Name midstate;
};

/* --------------------------   Functions   --------------------------------- */

FATransition fatrans_create (Name, Name, Name, int);
void         fatrans_delete (FATransition);
int          fatrans_compare (FATransition, FATransition);
int          fatrans_compare_simple (FATransition, FATransition);

void          fatrans_list_delete (FATransList*);
FATransition  fatrans_list_insert (FATransList*, FATransition, int*);

FATransTable  fatrans_table_empty ();
void          fatrans_table_delete (FATransTable*);
FATransition  fatrans_table_insert (FATransTable*, FATransition);
FATransition  fatrans_table_find (FATransTable, FATransition);
void	      fatrans_table_display (FATransTable);

#define LIST_END (FATransition)(1)

#endif
