/* =========================================================================

   Definition der Funktionen zur Verwaltung von Buechi-Automaten

   ====================================================================== */

#include <stdio.h>
#include "ba.h"
#include "common.h"

BuechiAutomaton ba_empty ()
{
	BuechiAutomaton ba;

	ba.start_state  = 0;
	ba.states       = name_set_empty();
	ba.transitions  = NULL;

	return ba;
}


void ba_delete (BuechiAutomaton *ba)
{
	BATransition t;

	while (ba->transitions)
	{
		t = ba->transitions;
		ba->transitions = t->next;
		ftree_delete(t->condition);
		common_free(t,sizeof(struct BATransitionStruct));
	}
	name_set_delete(&(ba->states));
}


void ba_insert_trans (BuechiAutomaton *ba,
		      Name            from_state,
		      FormulaTree     condition,
		      Name            to_state)
{
	BATransition t;

	t = common_malloc(sizeof(struct BATransitionStruct));
	t->from_state = from_state;
	t->condition = condition;
	t->to_state = to_state;
	t->next = ba->transitions;
	ba->transitions = t;
}

void ba_dfs (BuechiAutomaton *ba, Name v, NameSet *states)
{
	BATransition t;

	name_set_insert(states,v);
	for (t = ba->transitions; t; t = t->next)
	{
		if (t->from_state != v) continue;
		if (!name_set_find(*states,t->to_state))
			ba_dfs(ba,t->to_state,states);
	}
}

void ba_canonicize (BuechiAutomaton* ba)
{
	BATransition t;
	NameNode n1, n2;
	Name fs, ts;

	n1 = name_tree_find(ba_nametree,ba->start_state);
	if (n1) ba->start_state = n1->refname;
	for (t = ba->transitions; t; t = t->next)
	{
		n1 = name_tree_find(ba_nametree,t->from_state);
		n2 = name_tree_find(ba_nametree,t->to_state);
		fs = n1? n1->refname : t->from_state;
		ts = n2? n2->refname : t->to_state;

		name_set_insert(&(ba->states),fs);
		name_set_insert(&(ba->states),ts);

		t->from_state = fs;
		t->to_state = ts;
	}
}

void ba_minimize (BuechiAutomaton* ba)
{
	BATransition t, t2, nt;
	NameSet states = NULL;

	ba_dfs(ba,ba->start_state,&states);
	t = ba->transitions; nt = NULL;
	while(t)
	{
		t2 = t->next;
		if (name_set_find(states,t->from_state))
		{
			t->next = nt;
			nt = t;
		}
		else
		{
			ftree_delete(t->condition);
			common_free(t,sizeof(struct BATransitionStruct));
		}
		t = t2;
			
	}
	ba->transitions = nt;
}
