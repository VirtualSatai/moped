/* =========================================================================

   Definition der Datenstrukturen und Funktionen
   zur Verwaltung von Transitionen

   ====================================================================== */

#include <string.h>
#include <stdio.h>
#include <math.h>
#include <stdio.h>

#include "heads.h"
#include "common.h"


/* ----------------------------------------------------------------------- */
/* ---------------------------  Head  ------------------------------------ */
/* ----------------------------------------------------------------------- */


Head head_create(Name state, Name name)
{
	Head newhead = common_malloc(sizeof(struct HeadStruct));

	newhead->state  = state;
	newhead->name   = name;

	newhead->rules  = NULL;	/* contains list of neighbouring heads */
	newhead->fwd	= NULL;	/* list of forward neighbouring heads */
	newhead->stack  = NULL;	/* for linking all the repeating heads */
	newhead->list   = NULL;	/* for linking all heads in the head table */
	newhead->vstack = NULL;	/* for computation of rh */
	newhead->next   = NULL;	/* for use inside hash table */

	newhead->post	= NULL; /* collects rules starting with (state,name) */

	newhead->comp  = newhead->dfsnum = 0;
	Cudd_Ref(newhead->trans = emptyset);
	Cudd_Ref(newhead->rel = emptyset);
	newhead->hash  = state * state + name * name * 2;

	return newhead;
}


void head_delete (Head head)
{
	while (head->rules)
	{
		Rule r = head->rules->next;
		common_free(head->rules,sizeof(struct RuleStruct));
		head->rules = r;
	}
	common_free(head,sizeof(struct HeadStruct));
}


/* ----------------------------------------------------------------------- */
/* -----------------------------  HeadList  ------------------------------ */
/* ----------------------------------------------------------------------- */


int head_compare (Head h1, Head h2)
{
	int cmp;
	if ((cmp = name_compare(h1->state,h2->state))) return cmp;
	return name_compare(h1->name,h2->name);
}


Head head_list_insert (Head *list, Head newhead, int *newentry)
{
	Head last_entry = NULL;
	Head next_entry = *list;
	int cmp = 1;

	/* Einfuegeposition suchen */

	while (next_entry)
	{
		cmp = head_compare(next_entry,newhead);
		if (cmp >= 0) break;
		last_entry = next_entry;
		next_entry = next_entry->next;
	}

	if ((*newentry = cmp))
	{
		if (last_entry)
		{
			/* mittlere oder Endposition */
			newhead->next = next_entry;
			last_entry->next = newhead;
		}
		else
		{
			/* ganz vorne in Liste einfuegen */
			newhead->next = *list;
			*list = newhead;
		}
		return newhead;
	}
	else
	{
		head_delete(newhead);
		return next_entry;
	}
}


void head_add_rule (Head head, Head to, Name tail, int b, int new,
			PDSTransition origin, Name midstate, DdNode *vars)
{
	Rule rule;

	for (rule = head->rules; rule; rule = rule->next)
		if (rule->head == to && rule->b == b && rule->new == new
			&& rule->tail == tail && rule->origin == origin
			&& rule->midstate == midstate)
		{
			DdNode *tmp0;
			Cudd_Ref(tmp0 = Cudd_bddOr(mc_mgr,vars,rule->vars));
			Cudd_RecursiveDeref(mc_mgr,rule->vars);
			rule->vars = tmp0;
			return;
		}

	rule = common_malloc(sizeof(struct RuleStruct));
	rule->b = b;
	rule->new = new;
	rule->head = to;
	rule->headfwd = head;
	rule->tail = tail;
	rule->origin = origin;
	rule->midstate = midstate;
	rule->next = head->rules;
	rule->fwdnext = to->fwd;
	Cudd_Ref(rule->vars = vars);
	head->rules = to->fwd = rule;
}


/* ----------------------------------------------------------------------- */
/* ----------------------------  HeadTable  ------------------------------ */
/* ----------------------------------------------------------------------- */

HeadTable head_table_empty ()
{
	HeadTable new_table;
	int i;

	new_table.data = common_malloc(HEAD_HASH_MIN * sizeof(Head*));
	new_table.size = HEAD_HASH_MIN;
	new_table.mask = HEAD_HASH_MIN - 1;
	new_table.fill = 0;
	new_table.list = NULL;

	for (i = 0; i < new_table.size; i++) new_table.data[i] = NULL;
	return new_table;
}


void head_table_delete (HeadTable *table)
{
	long i;

	for (i = 0; i < table->size; i++)
	{
		Head list = table->data[i];
		while (list)
		{
			Head nexthead = list->next;
			head_delete(list);
			list = nexthead;
		}
	}

	common_free (table->data,table->size * sizeof(Head*));
}


Head head_table_insert (HeadTable *table, Head head)
{
	int hash = head->hash & table->mask;
	int newtrans, i;

	head = head_list_insert(&(table->data[hash]),head,&newtrans);

	if (!newtrans) return head;

	head->list = table->list;
	table->list = head;

	if (table->fill++ < table->size * 3/4) return head;

	table->data = common_realloc(table->data, table->size*2 * sizeof(Head*),
				     table->size * sizeof(Head*));

	table->mask = table->size * 2 - 1;

	for (i = 0; i < table->size; i++)
	{
		Head l1 = NULL, l2 = NULL;
		Head last_entry, next_entry;

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
	return head;
}


Head head_find (HeadTable table, Name state, Name name)
{
	Head head = head_create(state,name);
	Head list = table.data[head->hash & table.mask];

	while (list)
	{
		int cmp = head_compare(list,head);
		if (cmp > 0) list = NULL;
		if (cmp >= 0) break;
		list = list->next;
	}

	head_delete(head);
	return list;
}

