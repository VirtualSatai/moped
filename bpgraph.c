#include "bpstruc.h"
#include "common.h"
#include "sort.h"

extern int mc_poststar;
extern int mc_restrict;
extern int mc_verbose;
extern int mc_stats;
extern int mc_globals;

bp_dep_t bp_depnodes;
int* bp_dep_sp;

void bp_deps_seq (bp_fun_t,bp_stmt_t);

#define bp_d_getptr(id) (bp_depnodes + (id->fun? bp_maxrets + id->index : id->index))

/***************************************************************************/

void bp_dep_add (bp_dep_t v1, bp_dep_t v2)
{
	bp_ptr_t ni;

	for (ni = v1->edges; ni; ni = ni->next)
		if (ni->dep == v2) return;

	ni = alloc_bp_ptr();	// fixme: we should sort the v2 here
	ni->dep = v2;
	ni->next = v1->edges;
	v1->edges = ni;
	v2->inedges++;
}

/***************************************************************************/

void bp_dep_doexpr (bp_dep_t var, bp_expr_t expr)
{
	switch (expr->token)
	{
	  case BP_EQ:
	  case BP_NE:
	  case BP_AND:
	  case BP_OR:
	  case BP_IMP:
	  case BP_CHOOSE:
		bp_dep_doexpr(var,expr->right);
	  case BP_NOT:
		bp_dep_doexpr(var,expr->left);
		return;
	  case BP_IDENT: {
		bp_ident_t id = ((bp_idref_t)(expr->left))->ident;
		bp_dep_add(var,bp_d_getptr(id)); }
	  case BP_CONST:
	  case BP_ND:
		return;
	  default:
		common_error("can't happen");
	}	
}

/***************************************************************************/

void bp_deps_assign (bp_fun_t fun, bp_stmt_t stmt)
{
	bp_idref_t ref;

	for (ref = stmt->e.a.asgnlist; ref; ref = ref->next)
		bp_dep_doexpr(bp_d_getptr(ref->ident),ref->expr);
}

/***************************************************************************/

void bp_deps_call (bp_fun_t fun, bp_stmt_t stmt)
{
	bp_idref_t ref;
	bp_ident_t parm;
	bp_fun_t target = (bp_fun_t)bp_lookup(bp_funtree,stmt->e.a.label,-1);

	if (!target) common_error("function %s does not exist",
					name_cstring(stmt->e.a.label));

	for (ref = stmt->e.a.fmllist, parm = target->parms; 
			ref; ref = ref->next, parm = parm->next)
		bp_dep_doexpr(bp_d_getptr(parm),ref->expr);

	for (ref = stmt->e.a.asgnlist, parm = target->returns;
			ref; ref = ref->next, parm = parm->next)
		bp_dep_add(bp_d_getptr(ref->ident),bp_d_getptr(parm));
}

/***************************************************************************/

void bp_deps_if (bp_fun_t fun, bp_stmt_t stmt)
{
	bp_deps_seq (fun,stmt->e.c.thenstmt);
	bp_deps_seq (fun,stmt->e.c.elsestmt);
}

/***************************************************************************/

void bp_deps_while (bp_fun_t fun, bp_stmt_t stmt)
{
	bp_deps_seq (fun,stmt->e.c.thenstmt);
}

/***************************************************************************/

void bp_deps_return (bp_fun_t fun, bp_stmt_t stmt)
{
	bp_idref_t ref;
	bp_ident_t parm;

	for (ref = stmt->e.a.asgnlist, parm = fun->returns;
			ref; ref = ref->next, parm = parm->next)
		bp_dep_doexpr(bp_d_getptr(parm),ref->expr);
}

/***************************************************************************/

void bp_deps_seq (bp_fun_t fun, bp_stmt_t stmt)
{
	void (*cfun)(bp_fun_t,bp_stmt_t);

	while (stmt)
	{
		cfun = NULL;
	    switch (stmt->type)
	    {
			case BP_ASSIGN:
				cfun = bp_deps_assign; break;
			case BP_CALL:
				cfun = bp_deps_call; break;
			case BP_IF:
				cfun = bp_deps_if; break;
			case BP_WHILE:
				cfun = bp_deps_while; break;
			case BP_RETURN:
				cfun = bp_deps_return; break;
			case BP_ASSERT:
			case BP_ASSUME:
			case BP_CONSTRAIN:
			case BP_PRINT:
			case BP_SKIP:
			case BP_GOTO:
			default:
				cfun = NULL; break;
	    }
		
	    if (cfun) cfun(fun,stmt);

	    stmt = stmt->next;
	}
}

/***************************************************************************/

void bp_deps_fun (bp_fun_t fun)
{
//	bp_ident_t var, cb;

//	for (var = fun->locals, cb = fun->callbuf; var;
//			var = var->next, cb = cb->next)
//	{
//		if (cb->index < 0) continue;
//printf("companion of %d is %d\n",bp_maxrets+var->index,cb->index);
//		bp_depnodes[bp_maxrets + var->index].companion = cb->index + 1;
//		bp_depnodes[cb->index].companion = -1;
//	}

	bp_deps_seq(fun,fun->stmt);
}

/***************************************************************************/

void bp_dep_get_weight (bp_dep_t d)
{
	bp_ptr_t ni;
	bp_dep_t e;
	int wt = 1;

	d->weight = -1;

	for (ni = d->edges; ni; ni = ni->next)
	{
		e = ni->dep;
		if (e->marked) wt += e->weight;
		else if (e->weight == -1) ni->dep = NULL;
		else
		{
			bp_dep_get_weight(e);
			wt += e->weight;
		}
	}

	d->weight = wt;
	d->marked = 1;
}

/***************************************************************************/

void bp_dep_add_index (int index)
{
	if (index < bp_maxrets)
	{
		*bp_dep_sp++ = ppvars - pvars + index,	/* p', p, q */
		*bp_dep_sp++ = index,
		*bp_dep_sp++ = qvars - pvars + index;
		if (mc_verbose > 1) printf("added global %d\n",index);
	}
	else
	{
		index -= bp_maxrets;		/* y'', y', y', y''' */
		*bp_dep_sp++ = yppvars - bddvars + index,
		*bp_dep_sp++ = ypvars - bddvars + index,
		*bp_dep_sp++ = yvars - bddvars + index;
		if (mc_poststar && !mc_restrict)
			*bp_dep_sp++ = ypppvars - bddvars + index;
		if (mc_verbose > 1) printf("added local %d\n",index);
	}
}

void bp_dep_add_vars (bp_dep_t d)
{
	bp_ptr_t ni;
	int c = 0, c2 = 0;

	d->marked = 2;

	if (d->companion < 0) return;

	for (ni = d->edges; ni; ni = ni->next)
		if (ni->dep && ni->dep->marked == 1) c++;

	if (c == 1)
	{
		for (ni = d->edges; ni; ni = ni->next)
			if (ni->dep && ni->dep->marked == 1)
				bp_dep_add_vars(ni->dep);
	}
	else if (c)
	{
		bp_iwp_t iwp = malloc(c * sizeof(struct bp_iwp_element));
		for (ni = d->edges; ni; ni = ni->next)
			if (ni->dep && ni->dep->marked == 1)
			{
				iwp[c2].i = ni->dep->weight;
				iwp[c2++].p = ni->dep;
			}
		sort_iwp_rev(iwp,0,c-1);
		for (c2 = 0; c2 < c; c2++)
			if (((bp_dep_t)(iwp[c2].p))->marked == 1)
				bp_dep_add_vars((bp_dep_t)(iwp[c2].p));
		free(iwp);
	}

	bp_dep_add_index(d - bp_depnodes);
	if (d->companion) bp_dep_add_index(d->companion - 1);
}

/***************************************************************************/

void bp_dep_reverse_edges ()
{
	bp_dep_t d;
	int i;

	for (i = 0, d = bp_depnodes; i < bp_maxrets + bp_maxlocs; i++, d++)
		if (!d->inedges && d->edges && !d->edges->next)
		{
			bp_dep_add(d->edges->dep,d);
			free(d->edges);
			d->edges = NULL;
		}
}

/***************************************************************************/

void bp_dep_handle_globals ()
{
	bp_ident_t var;

	for (var = bp_globals; var; var = var->next)
	{
		bp_depnodes[var->index].companion = bp_maxrets + bp_savedglobals[var->index] + 1;
		bp_depnodes[bp_maxrets + bp_savedglobals[var->index]].companion = -1;
	}
}

/***************************************************************************/

void bp_reorder_dep ()
{
	bp_fun_t fun;
	bp_dep_t d;
	bp_iwp_t iwp, iwt;
	int i;

	mc_shuffle = malloc((GLOBALS + LOCALS + 1) * sizeof(int));
	mc_shuffle[0] = bvars - bddvars;
	bp_dep_sp = mc_shuffle + 1;
	
	bp_depnodes = malloc((bp_maxrets + bp_maxlocs) * sizeof(struct bp_dep_element));
	memset(bp_depnodes,0,(bp_maxrets + bp_maxlocs) * sizeof(struct bp_dep_element));

	if (mc_stats) printf("Initial ordering is by dependencies.\n\n");
	if (mc_verbose) printf("globals = %d, locals = %d\n",bp_maxrets,bp_maxlocs);	

	for (fun = bp_functions; fun; fun = fun->next)
		bp_deps_fun(fun);

	if (mc_globals) bp_dep_handle_globals();

	bp_dep_reverse_edges();

	for (i = 0, d = bp_depnodes; i < bp_maxrets + bp_maxlocs; i++, d++)
		if (!d->marked) bp_dep_get_weight(d);

	iwp = malloc((bp_maxrets + bp_maxlocs) * sizeof(struct bp_iwp_element));
	for (i = 0, d = bp_depnodes, iwt = iwp; i < bp_maxrets + bp_maxlocs; i++, d++, iwt++)
		iwt->i = d->weight, iwt->p = d;
	sort_iwp_rev(iwp,0,bp_maxrets + bp_maxlocs - 1);
	for (i = 0, iwt = iwp; i < bp_maxrets + bp_maxlocs; i++, iwt++)
		if (((bp_dep_t)iwt->p)->marked != 2) bp_dep_add_vars((bp_dep_t)iwt->p);

	if (bp_dep_sp - mc_shuffle < GLOBALS + LOCALS + 1)
		common_error("didn't catch all");

	free(bp_depnodes);	// fixme: oh, and all the edges...
	free(iwp);
}
