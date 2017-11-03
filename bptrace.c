#include <string.h>
#include "bpstruc.h"
#include "mcheck.h"
#include "bdd.h"
#include "common.h"

/***************************************************************************/

Name bp_reach_target_label;

/***************************************************************************/

#define bpmt_add(prefix,var) (prefix##_perm[(var)->index] = 1)

void bp_make_tracemasks (bp_fun_t fun)
{
	bp_ident_t var, cb;
	bp_funedge_t edge;
	int i, j;

	int pe_nv = 0, se_nv = 0, is_nv = 0;
	
	int *pe_vars = malloc((GLOBALS + LOCALS + 1) * sizeof(int));
	int *se_vars = malloc((GLOBALS + LOCALS + 1) * sizeof(int));
	int *is_vars = malloc((GLOBALS + LOCALS + 1) * sizeof(int));

	int *pe_perm = malloc((GLOBALS + LOCALS + 1) * sizeof(int));
	int *se_perm = malloc((GLOBALS + LOCALS + 1) * sizeof(int));
	int *is_perm = malloc((GLOBALS + LOCALS + 1) * sizeof(int));

	/* make pe_mask */
	memset(pe_perm,0xff,(GLOBALS + LOCALS + 1) * sizeof(int));
	memset(se_perm,0xff,(GLOBALS + LOCALS + 1) * sizeof(int));
	memset(is_perm,0xff,(GLOBALS + LOCALS + 1) * sizeof(int));

	for (var = bp_globals; var; var = var->next)
		if (!mc_globals || fun->funnode->usedglob[var->index])
			bpmt_add(pe,ppvars[var->index]), bpmt_add(pe,qvars[var->index]),
			bpmt_add(se,pvars[var->index]), bpmt_add(se,qvars[var->index]),
			bpmt_add(is,pvars[var->index]);
	
	if (stepwise(fun->num_returns))
		for (var = fun->returns; var; var = var->next)
			bpmt_add(pe,ppvars[var->index]);

	for (edge = fun->funnode->edges; edge; edge = edge->next)
	{
		bp_fun_t target = edge->fn->fun;

		for (var = target->returns; var; var = var->next)
			bpmt_add(pe,ppvars[var->index]);

		for (var = target->parms; var; var = var->next)
		{
			if (stepwise(target->num_args))	bpmt_add(pe,ypvars[var->index]);
			bpmt_add(se,yvars[var->index]), bpmt_add(is,yvars[var->index]);
		}

		if (call_crosses_comp(fun,target))
			for (var = bp_globals; var; var = var->next)
				if (fun->funnode->usedglob[var->index]
						&& !target->funnode->usedglob[var->index])
					bpmt_add(pe,ypvars[bp_savedglobals[var->index]]),
					bpmt_add(se,ypvars[bp_savedglobals[var->index]]),
					bpmt_add(se,yvars[bp_savedglobals[var->index]]),
					bpmt_add(is,yvars[bp_savedglobals[var->index]]);
	}

	for (var = fun->locals, cb = fun->callbuf; var;
		 var = var->next, cb = cb->next)
	{
		bpmt_add(pe,ypvars[var->index]), bpmt_add(se,ypvars[var->index]),
		bpmt_add(se,yvars[var->index]), bpmt_add(is,yvars[var->index]);

		if (cb->index >= 0)	bpmt_add(pe,ppvars[cb->index]),
			bpmt_add(se,pvars[cb->index]), bpmt_add(se,qvars[cb->index]),
			bpmt_add(is,pvars[cb->index]);
	}

	for (var = fun->parms; var; var = var->next)
		bpmt_add(pe,ypvars[var->index]), bpmt_add(pe,ypppvars[var->index]),
		bpmt_add(se,ypppvars[var->index]);

	for (i = j = 0; i < GLOBALS + LOCALS + 1; i++)
		if (pe_perm[i] > 0) { pe_vars[j] = i, pe_perm[i] = j, j++; }
	pe_nv = j;
	for (i = j = 0; i < GLOBALS + LOCALS + 1; i++)
		if (se_perm[i] > 0) { se_vars[j] = i, se_perm[i] = j, j++; }
	se_nv = j;
	for (i = j = 0; i < GLOBALS + LOCALS + 1; i++)
		if (is_perm[i] > 0) { is_vars[j] = i, is_perm[i] = j, j++; }
	is_nv = j;

	fun->pe_mask = alloc_bp_mask();
	fun->pe_mask->nv = pe_nv; 
	fun->pe_mask->perm = pe_perm;
	fun->pe_mask->vars = pe_vars;
	
	fun->se_mask = alloc_bp_mask();
	fun->se_mask->nv = se_nv; 
	fun->se_mask->perm = se_perm;
	fun->se_mask->vars = se_vars;
	
	fun->is_mask = alloc_bp_mask();
	fun->is_mask->nv = is_nv; 
	fun->is_mask->perm = is_perm;
	fun->is_mask->vars = is_vars;
}

DdNode* bp_find_one(DdNode *bdd, int useq, Name local)
{
	DdNode *tb, *cube;
	DdNode **v = malloc((GLOBALS+LOCALS) * sizeof(DdNode*));
	bp_mask_t mask = NULL;
	int i, branch, inv = 0;

	bp_fun_t fun = (bp_fun_t) bp_find_var(bp_labeltree,local,-2);

	if (useq == 0) mask = fun->is_mask;
	if (useq == 4) mask = fun->pe_mask;
	if (useq == 5) mask = fun->se_mask;

	for (i = 0; i < mask->nv; i++)
		v[i] = Cudd_Not(bddvars[mc_shuffle[mask->vars[i]]]);
		
	while (Cudd_Regular(bdd)->index != 0xffff)
	{
		inv = inv ^ Cudd_IsComplement(bdd);
		bdd = Cudd_Regular(bdd);
		tb = Cudd_Regular(Cudd_T(bdd));
		branch = (tb->index != 0xffff ||
		   (!!tb->type.value ^ inv ^ Cudd_IsComplement(Cudd_T(bdd))));
		if (branch)
		{
			int index = mask->perm[bdd->index];
			if (index != -1) v[index] = bddvars[mc_shuffle[bdd->index]];
		}
		bdd = branch? Cudd_T(bdd) : Cudd_E(bdd);
	}

	cube = Cudd_bddComputeCube(mc_mgr,v,NULL,mask->nv);
	free(v);
	return cube;
}

/***************************************************************************/

void bp_print_state (FILE *file, DdNode *bdd, void (*printfn)(FILE*,bp_ident_t,int),
					 int local, char useprimes)
{
	DdNode *tb;
	bp_ident_t blk = ((bp_fun_t)bp_find_var(bp_labeltree,local,-2))->locals;
	char inv = 0, branch;

	while (Cudd_Regular(bdd)->index != 0xffff)
	{
		inv ^= Cudd_IsComplement(bdd);
		bdd = Cudd_Regular(bdd);
		tb = Cudd_Regular(Cudd_T(bdd));
		branch = (tb->index != 0xffff ||
		   (!!tb->type.value ^ inv ^ Cudd_IsComplement(Cudd_T(bdd))));
		bddval[mc_shuffle[bdd->index]] = branch;
		bdd = branch? Cudd_T(bdd) : Cudd_E(bdd);
	}

	if (!useprimes) printfn(file,bp_globals,0);				/* p  */
	if (useprimes)  printfn(file,bp_globals,ppvars-pvars);	/* p' */
	if (!useprimes) printfn(file,blk,yvars-pvars);			/* y  */
	if (useprimes)  printfn(file,blk,ypvars-pvars);			/* y' */
}

/***************************************************************************/

void bpn_print_bddvars (FILE *file, bp_ident_t blk, int offset)
{
	for (; blk; blk = blk->next)
	{
		if (*name_cstring(blk->varname) != '{') continue;
		fprintf(file,"%s=%d ",
			name_cstring(blk->varname),bddval[offset + blk->index]);
	}
}

void bp_output_path_post (FILE *file, Path p, char post)
{
	DdNode *tmp0;
	char *colon;

	colon = strchr(name_cstring(p->t->name),':');
	if (!colon) return;

	if (!strncmp(colon+1,"c2bp_b_",7))
	{
		fprintf(file,"%s\n",colon+8);
		return;
	}

	if (strncmp(colon+1,"c2bp_i_",7)) return;

	/* tmp0 = ex q,y''': p->bdd */
	Cudd_Ref(tmp0 = Cudd_bddExistAbstract(mc_mgr,p->bdd,mc_cube8));
	bp_print_state(file,tmp0,bpn_print_bddvars,p->t->name,post);
	fprintf(file,";\n");
	Cudd_RecursiveDeref(mc_mgr,tmp0);
}

/***************************************************************************/

void bp_get_trace_newton (Path path, char post)
{
	FILE *file;
	char *filename = malloc(strlen(bp_trace_fileprefix)+6);

	sprintf(filename,"%s.p",bp_trace_fileprefix);
	if (!(file = fopen(filename,"w")))
		common_error("could not open trace file %s for writing",
			filename);
	free(filename);
	
	/* go to the end */
	if (post) while (path->nextconf) path = path->nextconf;

	/* traverse from end to beginning */
	while (path)
	{
		bp_output_path_post(file,path,post);
		// fixme: clean the old path up
		path = path->prevconf;
	}
	
	fclose(file);
}

/***************************************************************************/
/***************************************************************************/

Traj bpx_done, bpx_worklist;
bp_tree_t bpx_fmap, bpx_vmap;

int bpx_traj_comp (Traj t1, Traj t2)
{
	if (t1->result != t2->result) return 1;
	if (t1->first->t->from_state != t2->first->t->from_state) return 1;
	if (t1->first->t->name != t2->first->t->name) return 1;
	if (t1->last->t->from_state != t2->last->t->from_state) return 1;
	if (t1->last->t->name != t2->last->t->name) return 1;
	return 0;
}

int bpx_add_to_worklist (Traj tj)
{
	Traj tmp;

	if (!tj->result) return tj->nr;
	// fixme: bad linear search
	for (tmp = bpx_done; tmp; tmp = tmp->next)
		if (!bpx_traj_comp(tmp,tj)) return tmp->nr;
	for (tmp = bpx_worklist; tmp; tmp = tmp->next)
		if (!bpx_traj_comp(tmp,tj)) return tmp->nr;

	tj->next = bpx_worklist;
	bpx_worklist = tj;
	return tj->nr;
}

void bpx_print_stmt_hdr (FILE *file, int index, Name cfile, Name realfun, 
						 int line, int entry)
{
	fprintf(file,"<path:stmt index=\"%d\" "
		"file=\"%s\" proc=\"%s\" line=\"%d\" %sentry=\"true\">\n",
		index,name_cstring(cfile),name_cstring(realfun),line,
		entry? "" : "not");
}

void bpx_print_bddvars (FILE *file, bp_ident_t blk, int offset)
{
	bp_ident_t id;

	for (; blk; blk = blk->next)
	{
		if (*name_cstring(blk->varname) != '{') continue;

		id = bp_lookup(bpx_vmap,blk->varname,0);

		fprintf(file,"  <env:pair>\n    <env:var name=\"%s\" scope=\"%s\" "
					"sortscope=\"%d\"/>\n    <env:val value=\"%d\"/>\n"
					"  </env:pair>\n",
				name_cstring(id? id->varname : blk->varname),
				blk->fun? "local" : "global", blk->fun? 1 : 0,
				bddval[offset + blk->index]);
	}
}

void bpx_print_state (FILE *file, Path p, char post)
{
	DdNode *tmp0;

	/* tmp0 = ex q,y''': p->bdd */
	Cudd_Ref(tmp0 = Cudd_bddExistAbstract(mc_mgr,p->bdd,mc_cube8));

	fprintf(file,"<env:state xmlns:env=\"x-schema:envschema.xml\">\n");
	bp_print_state(file,tmp0,bpx_print_bddvars,p->t->name,post);
	fprintf(file,"</env:state>\n");

	Cudd_RecursiveDeref(mc_mgr,tmp0);
}

void bpx_output_xml_trace (Traj tj, char post)
{
	bp_fun_t fun = (bp_fun_t)bp_find_var(bp_labeltree,tj->first->t->name,-2);
	bp_ident_t id = bp_lookup(bpx_fmap,fun->funname,0);

	FILE *file;
	Path p1;
	char *filename;
	int stmtindex = 0;

	if (!id)
	{
		id = alloc_bp_ident();
		id->index = name_create("??");
		id->varname = fun->funname;
	}

	filename = malloc(strlen(bp_trace_fileprefix) +
					  strlen(name_cstring(bp_reach_target_label)) + 
					  strlen(name_cstring(fun->funname)) + 16);

	sprintf(filename,"%s.%s.%s.%d.xml",
		bp_trace_fileprefix,name_cstring(bp_reach_target_label),
		name_cstring(fun->funname),tj->nr);
	if (!tj->nr)
		sprintf(filename,"%s.%s.xml",
			bp_trace_fileprefix,name_cstring(bp_reach_target_label));

	if (!(file = fopen(filename,"w")))
		common_error("could not open trace file %s for writing",filename);
	free(filename);

	fprintf(file,"<?xml version='1.0'?>\n"
			"<path:path name=\"%d\" xmlns:path=\"x-schema:pathschema.xml\"\n"
			"xmlns:env=\"x-schema:envschema.xml\">\n",tj->nr);

	for (p1 = tj->last; p1; p1 = p1->prevconf)
	{
		int line = 0;

		char *tmp = strchr(name_cstring(p1->t->name),':');

		if (tmp && tmp[1] == 'C' && tmp[2] == '_') line = atoi(tmp+3);

		if (p1->traj)
		{
			bp_fun_t target = (bp_fun_t) bp_find_var(bp_labeltree,p1->traj->first->t->name,-2);
			char *targetname = name_cstring(target->funname);
			bp_ident_t targetid = bp_lookup(bpx_fmap,target->funname,0);
			int trajnr = bpx_add_to_worklist(p1->traj);

			if (!strncmp(targetname,"SLIC",4)) continue;
			if (!strcmp(targetname,"choose")) continue;
			if (!strcmp(targetname,"unk")) continue;
			if (!strncmp(targetname,"__init",6)) continue;

			bpx_print_stmt_hdr(file,stmtindex++,id->index,id->varname,
							   line,p1==tj->last);
			bpx_print_state(file,p1,post);
			fprintf(file,"<path:call caller=\"%s\" callee=\"%s\" code=\"--\" "
						 "src=\"%s.%s.%s.%d.xml\"/>\n"
						 "</path:stmt>\n\n",
				name_cstring(id->varname),targetid? name_cstring(targetid->varname) : targetname,
				bp_trace_fileprefix,name_cstring(bp_reach_target_label),
				targetname,trajnr);
		}
		else if (line)
		{
			bpx_print_stmt_hdr(file,stmtindex++,id->index,id->varname,
							   line,p1==tj->last);
			bpx_print_state(file,p1,post);
			fprintf(file,"<path:default code=\"--\">\n"
						 "</path:default>\n"
						 "</path:stmt>\n\n");
		}
	}
	
	fprintf(file,"</path:path>\n");
	
	fclose(file);
}

void bpx_get_result (Traj tj, char post)
{
	DdNode *tmp0, *tmp1;

	/* tmp1 = (ex q,y''': tj->last->bdd)(p'->p,y'->y)/(p->p',y->y') */
	Cudd_Ref(tmp0 = Cudd_bddExistAbstract(mc_mgr,tj->last->bdd,mc_cube8));
	Cudd_Ref(tmp1 = Cudd_bddPermute(mc_mgr,tmp0,post? mc_perm1 : mc_perm6));
	Cudd_RecursiveDeref(mc_mgr,tmp0);

	/* tmp0 = ex q,y''': tj->first->bdd */
	Cudd_Ref(tmp0 = Cudd_bddExistAbstract(mc_mgr,tj->first->bdd,mc_cube8));

	Cudd_Ref(tj->result = Cudd_bddAnd(mc_mgr,tmp0,tmp1));
	Cudd_RecursiveDeref(mc_mgr,tmp0);
	Cudd_RecursiveDeref(mc_mgr,tmp1);
}

Traj bpx_split_open_trajectories (Path path, char post)
{
	Traj bpx_tj, newtj;
	int bpx_tjcount = 0;

	bpx_tj = malloc(sizeof(struct TrajElementStruct));

	if (!post) while (path->prevconf) path = path->prevconf;

	bpx_tj->first = path;
	bpx_tj->nr = bpx_tjcount++;
	bpx_tj->next = NULL;

	while (path->nextconf)
	{
		char *label = (post? path->nextconf : path)->l->pt->label;		

		path = path->nextconf;
		if (!label)
			path->prevconf->traj = NULL;
		else if (!strcmp(label,"call"))
		{
			newtj = malloc(sizeof(struct TrajElementStruct));
			newtj->first = path;
			newtj->nr = bpx_tjcount++;
			newtj->next = bpx_tj;
			bpx_tj = newtj;
		}
		else if (!strcmp(label,"return"))
		{
			path->prevconf->traj = NULL;
			bpx_tj->last = path->prevconf;
			bpx_tj->first->prevconf->traj = bpx_tj;
			bpx_tj->first->prevconf->nextconf = path;
			path->prevconf->nextconf = NULL;
			path->prevconf = bpx_tj->first->prevconf;
			bpx_tj->first->prevconf = NULL;
			bpx_get_result(bpx_tj,post);
			bpx_tj = bpx_tj->next;
		}
		else
			path->prevconf->traj = NULL;
	}

	path->traj = NULL;
	bpx_tj->last = path;
	bpx_tj->result = NULL;
	for (newtj = bpx_tj; newtj->next; newtj = newtj->next)
	{
		newtj->next->result = NULL;
		newtj->next->last = newtj->first->prevconf;
		newtj->first->prevconf = NULL;
		newtj->next->last->nextconf = NULL;
		newtj->next->last->traj = newtj;
	}

	return bpx_tj;
}

void bpx_setup_fmap ()
{
	FILE *file;
	char *filename;

	filename = malloc(strlen(bp_trace_fileprefix) + 3);
	sprintf(filename,"%s.f",bp_trace_fileprefix);
	if (!(file = fopen(filename,"r")))
		common_error("could not open trace file %s for reading",filename);
	free(filename);

	bpx_fmap = NULL;

	for (;;)
	{
		bp_ident_t id;
		char tmp[256];	// fixme
		Name bpfun, realfun, cfile;

		fscanf(file,"%s",tmp);
		if (feof(file)) break;

		bpfun = name_create(tmp);
		fscanf(file,"%s",tmp);
		realfun = name_create(tmp);
		fscanf(file,"%s",tmp);
		cfile = name_create(tmp);

		id = alloc_bp_ident();
		id->varname = realfun;
		id->index = cfile;
		bp_insert_decl(&bpx_fmap,bpfun,0,id);
	}

	fclose(file);

}

void bpx_setup_vmap ()
{
	FILE *file;
	char *filename;

	filename = malloc(strlen(bp_trace_fileprefix) + 3);
	sprintf(filename,"%s.v",bp_trace_fileprefix);
	if (!(file = fopen(filename,"r")))
		common_error("could not open trace file %s for reading",filename);
	free(filename);

	bpx_vmap = NULL;

	for (;;)
	{
		bp_ident_t id;
		char tmp[256];	// fixme
		Name bpvar, realvar;

		fscanf(file,"%s",tmp);
		if (feof(file)) break;

		bpvar = name_create(tmp);
		fscanf(file,"%s",tmp);
		realvar = name_create(tmp);

		id = alloc_bp_ident();
		id->varname = realvar;
		bp_insert_decl(&bpx_vmap,bpvar,0,id);
	}

	fclose(file);
}

void bp_get_trace_xml (Path path, char post)
{
	Traj bpx_tj;

	bpx_setup_fmap();
	bpx_setup_vmap();

	bpx_tj = bpx_split_open_trajectories(path,post);
	bpx_done = bpx_worklist = NULL;

	while (bpx_tj)
	{
		bpx_output_xml_trace(bpx_tj,post);
		bpx_tj = bpx_tj->next;
		/* fixme: free the trajectory pointers */
	}

	while (bpx_worklist)
	{
		bpx_tj = bpx_worklist;
		bpx_worklist = bpx_tj->next;
		bpx_tj->next = bpx_done;
		bpx_done = bpx_tj;
		bpx_output_xml_trace(bpx_tj,post);
	}
}
