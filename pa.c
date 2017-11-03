
/* =========================================================================

	Functions for printing the automata for reachable configurations

   ====================================================================== */

#include <string.h>
#include <stdio.h>

#include "common.h"
#include "fatrans.h"
#include "mcheck.h"

void print_post_automaton (FATransTable *table)
{
	FATransition t;
	DdNode *tmp0;
	int i;

	printf("\n--- START FA ---\n");
	for (i = 0; i < table->size; i++)
	    for (t = table->data[i]; t; t = t->next)
	    {
		Name toctrl = 0, tostack = 0;

		char *fs = name_cstring(t->from_state);
		char *nm = name_cstring(t->name);
		char *ts = name_cstring(t->to_state);

		if (t->rel == emptyset) continue;
		if (*fs == '$') continue;
		printf("%s -[%s]-> %s\n",fs,nm,ts);
		if (mc_reach < 3) continue;

		if (mc_reach < 4)
		{
			if (*fs == '^') continue;

			/* tmp0 = ex q,y''': t->rel */
			Cudd_Ref(tmp0 = Cudd_bddExistAbstract
				(mc_mgr,t->rel,mc_cube8));
			
			print_bdd(tmp0,post_set_front,0,t->name,0,0);
			Cudd_RecursiveDeref(mc_mgr,tmp0);
			continue;
		}

		if (*ts == '^')
			get_names_from_state(t->to_state,&toctrl,&tostack);

		if (*fs == '^')
		{
			Name fctrl, fstack;
			get_names_from_state(t->from_state,&fctrl,&fstack);
			print_bdd(t->rel,post_set_mid,fstack,t->name,0,tostack);
		}
		else
		{
			print_bdd(t->rel,post_set_init,0,t->name,0,tostack);
		}
	    }

	printf("--- END FA ---\n\n");
}

void print_pre_automaton (FATransTable *table)
{
	FATransition t;
	DdNode *tmp0;
	int i;

	printf("\n--- START FA ---\n");
	for (i = 0; i < table->size; i++)
	    for (t = table->data[i]; t; t = t->next)
	    {
		char *fs = name_cstring(t->from_state);
		char *nm = name_cstring(t->name);
		char *ts = name_cstring(t->to_state);

		if (t->rel == emptyset) continue;
		if (*fs == '$') continue;
		printf("%s -[%s]-> %s\n",fs,nm,ts);
		if (mc_reach < 3) continue;

		if (mc_reach < 4)
		{
			/* tmp0 = ex q: t->rel */
			Cudd_Ref(tmp0 = Cudd_bddExistAbstract
				(mc_mgr,t->rel,mc_cube2));
			
			print_bdd(tmp0,pre_set_front,t->name,0,0,0);
			Cudd_RecursiveDeref(mc_mgr,tmp0);
		}
		else
		{
			print_bdd(t->rel,pre_set_all,t->name,0,0,0);
		}
	    }

	printf("--- END FA ---\n\n");
}
