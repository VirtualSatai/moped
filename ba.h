/* =========================================================================

   Deklaration der Datenstrukturen und Funktionen
   zur Verwaltung von Buechi-Automaten

   ====================================================================== */

#ifndef BA_H
#define BA_H

#include "name.h"
#include "ftree.h"
#include "bdd.h"

typedef struct BuechiAutomatonStruct BuechiAutomaton;
typedef struct BATransitionStruct * BATransition;
typedef struct BATransitionStruct * BATransList;

extern NameTree ba_nametree;

struct BuechiAutomatonStruct
{
	NameSet states;
	Name start_state;
	BATransList transitions;
};

struct BATransitionStruct
{
	Name from_state;
	FormulaTree condition;
	Name to_state;
	BATransition next;
};

#define ba_is_finalstate(state) (!strncmp(name_cstring(state),"accept",6))

BuechiAutomaton ba_empty ();
void ba_delete (BuechiAutomaton*);
void ba_insert_trans (BuechiAutomaton*,Name,FormulaTree,Name);
void ba_canonicize (BuechiAutomaton*);
void ba_minimize (BuechiAutomaton*);

#endif
