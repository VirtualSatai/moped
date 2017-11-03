#include "heads.h"

int dfs_count, dfs_comp;
Head dfs_stack, dfs_found;

void dfs_search_recur (Head v)
{
	int found = 0;
	Rule rule;
	Head w;

	v->stack = dfs_stack;
	dfs_stack = v;
	v->lowpt = v->dfsnum = ++dfs_count;

	for (rule = v->fwd; rule; rule = rule->fwdnext)
	{
		w = rule->headfwd;
		if (!w->dfsnum)
		{
			dfs_search_recur(w);
			if (w->lowpt < v->lowpt) v->lowpt = w->lowpt;
		}
		if (!w->comp && w->dfsnum < v->lowpt) v->lowpt = w->dfsnum;
	}

	if (v->lowpt == v->dfsnum)
	{
		Head new_stack = v->stack;
		v->stack = NULL;

		dfs_comp++;
		for (w = dfs_stack; w; w = w->stack) w->comp = dfs_comp;

		for (w = dfs_stack; w; w = w->stack)
		    for (rule = w->rules; rule; rule = rule->next)
			if (rule->b && rule->head->comp == dfs_comp) found++;

		if (found) { v->stack = dfs_found; dfs_found = dfs_stack; }
		else for (w = dfs_stack; w; w = w->stack) w->comp = -dfs_comp;
		dfs_stack = new_stack;
	}
}

void dfs_search (Head v)
{
	dfs_count = dfs_comp = 0;
	dfs_stack = dfs_found = NULL;
	dfs_search_recur(v);
}

int find_circle(Head start, Head goal)
{
	Rule rule;

	if (start == goal) return 1;
	if (start->dfsnum) return 0;
	start->dfsnum = 1;

	for (rule = start->rules; rule; rule = rule->next)
	{
		if (rule->head->comp != goal->comp) continue;
		if (start->lowpt && rule->b) continue;
		if (find_circle(rule->head,goal)) break;
	}

	start->dfsnum = 0;
	return !!rule;
}

int find_k_cover (int k, Head start, Head vstart)
{
	Head head;
	Rule rule;

	if (!k)
	{
		for (head = vstart; head; head = head->vstack)
		{
		    if (head->lowpt) continue;
		    for (rule = head->rules; rule; rule = rule->next)
			if (rule->b && rule->head->comp == head->comp &&
				find_circle(rule->head,head)) return 0;
		}
		return 1;
	}

	if (!start) return 0;
	start->lowpt = 1;
	if (find_k_cover(k-1,start->vstack,vstart)) return 1;
	start->lowpt = 0;
	return find_k_cover(k,start->vstack,vstart);
}

void find_cover (Head start)
{
	Head vstart = NULL, head, nx, pv;
	Rule rule;
	int c, k;


	for (head = start; head && head->comp==start->comp; head = head->stack)
	{
		c = 0;
		for (rule = head->rules; rule; rule = rule->next)
			if (rule->head->comp == start->comp && rule->b) c++;
		if (!c) continue;
		head->dfsnum = c;
		head->lowpt = 0;
		for (nx = vstart, pv = NULL; nx && nx->dfsnum > c;
				pv = nx, nx = nx->vstack);
		head->vstack = nx;
		if (pv) pv->vstack = head; else vstart = head;
	}

	for (head = start; head && head->comp==start->comp; head = head->stack)
		head->dfsnum = 0;
	for (k = 1; !find_k_cover(k,vstart,vstart); k++);
	for (head = start; head && head->comp==start->comp; head = head->stack)
		head->vstack = NULL;
}
