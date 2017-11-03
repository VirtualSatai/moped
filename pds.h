/* =========================================================================

   Deklaration der Datenstrukturen und Funktionen
   zur Verwaltung von Pushdown Systemen

   ====================================================================== */

#ifndef PDS_H
#define PDS_H

#include "name.h"
#include "bdd.h"

/* --------------------------   Datatypes   --------------------------------- */

typedef struct PushdownSystemStruct PushdownSystem;
typedef struct PDSTransitionStruct* PDSTransition;
typedef struct PDSTransitionStruct* PDSTransList;

struct PushdownSystemStruct
{
	Name         start_state;
	NameStack    start_stack;
	DdNode*      start_bdd;
	PDSTransList transitions;
	PDSTransList lasttrans;
};

struct PDSTransitionStruct
{
	Name from_state;
	Name from_stack;
	Name to_state;
	Name to_stack1;
	Name to_stack2;

	Name midstate;
	char *label;
	DdNode *vars;
	int prio;

	PDSTransition next;
	PDSTransition post;
	char b;
};

/* --------------------------   Functions   --------------------------------- */

#define pds_is_finalstate(state) (state? ((*name_cstring(state)) == '$') : 0)
#define pdstrans_list_empty() NULL

PushdownSystem pds_empty ();
void		pds_delete (PushdownSystem*);
void		pds_display (PushdownSystem);
void		pds_insert_trans (PushdownSystem*, Name, Name, Name,
						   Name, Name, DdNode*, char*, int);
void		pds_prepare_check (PushdownSystem);
void		pds_print_trans (PDSTransition);

PDSTransition	pdstrans_create (Name, Name, Name, Name, Name, char*, int);
void		pdstrans_delete (PDSTransition);
void		pdstrans_list_delete (PDSTransList*);
void		pdstrans_list_insert (PushdownSystem*, PDSTransition, DdNode*);
void		pds_add_reach_target(PushdownSystem*,char*);

#endif
