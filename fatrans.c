/* =========================================================================

   Definition der Datenstrukturen und Funktionen
   zur Verwaltung von Transitionen

   ====================================================================== */

#include <string.h>
#include <stdio.h>

#include "common.h"
#include "fatrans.h"


/* ----------------------------------------------------------------------- */
/* ---------------------------  FATransition  ---------------------------- */
/* ----------------------------------------------------------------------- */


FATransition fatrans_create(Name from_state, Name name, Name to_state, int b)
{
	FATransition new_transition;

	new_transition = common_malloc(sizeof(struct FATransitionStruct));

	new_transition->from_state = from_state;
	new_transition->name       = name;
	new_transition->to_state   = to_state;

	new_transition->b	   = b;
	new_transition->f	   = 0;
	Cudd_Ref(new_transition->trans = emptyset);
	Cudd_Ref(new_transition->rel = emptyset);
	new_transition->origin     = NULL;
	new_transition->stack	   = NULL;
	new_transition->list	   = NULL;
	new_transition->next       = NULL;
	new_transition->prio       = 0;

	new_transition->hash = from_state * from_state + name * name * 2
				+ to_state * to_state * 6;

	return new_transition;
}


void fatrans_delete (FATransition transition)
{
	common_free(transition,sizeof(struct FATransitionStruct));
}


/* ------------------------------------------------------------------------- */
/* ----------------------------  FATransList  ------------------------------ */
/* ------------------------------------------------------------------------- */


void fatrans_list_delete (FATransList *trans_list)
{
	while (*trans_list)
	{
		FATransition entry = *trans_list;
		*trans_list = (*trans_list)->next;
		fatrans_delete(entry);
	}
}


FATransition fatrans_list_find (FATransList trans_list, FATransition transition)
{
	FATransition ret = NULL;

	while (trans_list && !ret)
	{
		int cmp = fatrans_compare_simple(trans_list,transition);

		if (cmp > 0) trans_list = NULL;
		if (cmp >= 0) break;
		trans_list = trans_list->next;
	}

	fatrans_delete(transition);
	return trans_list;
}


int fatrans_compare (FATransition t1, FATransition t2)
{
	int cmp;

	if ((cmp = name_compare(t1->from_state,t2->from_state))) return cmp;
	if ((cmp = name_compare(t1->name,t2->name))) return cmp;
	if ((cmp = name_compare(t1->to_state,t2->to_state))) return cmp;

	return -(t2->b != t1->b);
}


int fatrans_compare_simple (FATransition t1, FATransition t2)
{
	int cmp;

	if ((cmp = name_compare(t1->from_state,t2->from_state))) return cmp;
	if ((cmp = name_compare(t1->name,t2->name))) return cmp;
	return name_compare(t1->to_state,t2->to_state);
}


FATransition fatrans_list_insert (FATransList *trans_list,
				  FATransition new_transition, int *newtrans)
{
	FATransition last_entry = NULL;
	FATransition next_entry = *trans_list;
	int cmp = 1;

	/* Einfuegeposition suchen */

	while (next_entry)
	{
		cmp = fatrans_compare(next_entry,new_transition);
		if (cmp >= 0) break;
		last_entry = next_entry;
		next_entry = next_entry->next;
	}

	if ((*newtrans = cmp))
	{
		if (last_entry)
		{
			/* mittlere oder Endposition */
			new_transition->next = next_entry;
			last_entry->next = new_transition;
		}
		else
		{
			/* ganz vorne in Liste einfuegen */
			new_transition->next = *trans_list;
			*trans_list = new_transition;
		}
		return new_transition;
	}
	else
	{
		fatrans_delete(new_transition);
		return next_entry;
	}
}


FATransition fatrans_list_simple_insert (FATransList *trans_list,
					 FATransition new_transition)
{
	new_transition->next = *trans_list;
	*trans_list = new_transition;
	return new_transition;
}


/* ----------------------------------------------------------------------- */
/* ----------------------------  FATransTable  ----------------------------- */
/* ----------------------------------------------------------------------- */

FATransTable fatrans_table_empty ()
{
	FATransTable new_table;
	int i;

	new_table.data = common_malloc(FAT_HASH_MIN * sizeof(FATransList));
	new_table.size = FAT_HASH_MIN;
	new_table.mask = FAT_HASH_MIN - 1;
	new_table.fill = 0;
	new_table.usestack = 0;
	new_table.stack = NULL;
	new_table.list = NULL;

	for (i = 0; i < new_table.size; i++) new_table.data[i] = NULL;
	return new_table;
}


void fatrans_table_delete (FATransTable *trans_table)
{
	long i;

	for (i = 0; i < trans_table->size; i++)
		fatrans_list_delete(&(trans_table->data[i]));

	common_free (trans_table->data,trans_table->size * sizeof(FATransList));
}


FATransition fatrans_table_insert (FATransTable *table, FATransition trans)
{
	int hash = trans->hash & table->mask;
	int newtrans, i;

	trans = fatrans_list_insert(&(table->data[hash]),trans,&newtrans);

	if (!newtrans) return trans;

	if (table->usestack & FAT_USE_STACK)
	{
		trans->stack = table->stack;
		table->stack = trans;
	}

	if (table->usestack & FAT_USE_LIST)
	{
		trans->list = table->list;
		table->list = trans;
	}

	if (table->usestack & FAT_LIST_MARK) trans->list = LIST_END;

	if (table->fill++ < table->size * 3/4) return trans;

	table->data = common_realloc(table->data,
		table->size * 2 * sizeof(void*), table->size * sizeof(void*));

	table->mask = table->size * 2 - 1;

	for (i = 0; i < table->size; i++)
	{
		FATransition l1 = NULL, l2 = NULL;
		FATransition last_entry, next_entry;

		last_entry = table->data[i];
		while (last_entry)
		{
			next_entry = last_entry->next;
			if ((last_entry->hash & table->mask) == (unsigned long)i)
			{
				last_entry->next = l1;
				l1 = last_entry;
			}
			else
			{
				last_entry->next = l2;
				l2 = last_entry;
			}
			last_entry = next_entry;
		}

		last_entry = NULL;
		while (l1)
		{
			next_entry = l1->next;
			l1->next = last_entry;
			last_entry = l1;
			l1 = next_entry;
		}
		table->data[i] = last_entry;

		last_entry = NULL;
		while (l2)
		{
			next_entry = l2->next;
			l2->next = last_entry;
			last_entry = l2;
			l2 = next_entry;
		}
		table->data[i + table->size] = last_entry;

	}

	table->size *= 2;

	return trans;
}


FATransition fatrans_table_find (FATransTable table, FATransition trans)
{
	int hash = trans->hash & table.mask;
	return fatrans_list_find(table.data[hash],trans);
}

void fatrans_table_display (FATransTable table)
{
	FATransition t;
	int i;

        for (i = 0; i < table.size; i++)
                for (t = table.data[i]; t; t = t->next)
		{
			DdNode *tmp0;
			Cudd_Ref(tmp0 = Cudd_bddOr(mc_mgr,t->rel,t->trans));
            printf("%s-[%s]->%s\n",name_cstring(t->from_state),
                            name_cstring(t->name), name_cstring(t->to_state));
			Cudd_RecursiveDeref(mc_mgr,tmp0);
		}
}
