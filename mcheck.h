/* =========================================================================

	Declarations for variables and procedures from various files

   ====================================================================== */


#ifndef MCHECK_H
#define MCHECK_H

#include "bdd.h"
#include "heads.h"
#include "fatrans.h"
#include "bpstruc.h"

typedef struct PathElementStruct *Path;
typedef struct LoopElementStruct *Loop;
typedef struct TrajElementStruct *Traj;

struct PathElementStruct
{
	FATransition t;
	DdNode *bdd;
	OriginList l;
	Path next;
	Path nextconf;
	Path prevconf;
	Traj traj;
};

struct LoopElementStruct
{
	Head head;
	Loop next;
};

struct TrajElementStruct
{
	Path first;
	Path last;
	DdNode *result;
	int nr;
	Traj next;
};

extern PushdownSystem   mc_pds;
extern FATransTable     mc_trans, mc_index;
extern FATransTable     p_trans, p_index;
extern HeadTable        mc_heads, p_heads;
extern Name             mc_sstate;
extern Head             mc_starthead;
extern int		mc_poststar, mc_demand;
extern int		mc_reach;
extern int		mc_restrict;
extern int		mc_trace;
extern int		mc_verbose;
extern float		mctime_post, mctime_pre2;
extern float		mctime_head, mctime_pre3;
extern Head		dfs_found;
extern int		mc_age;
extern int		mc_bp;
extern int		mc_elimdead;
extern int		mc_globals;
extern int		mc_queue;
extern int		mc_stop_after_post;
extern int		mc_elimstuff;
extern int		mc_use_ba;

extern char		demand_finished;

extern Name bp_reach_target_label;
extern char *bp_trace_fileprefix;

/* mcheck.c */
extern void add_bdd_trans(FATransTable*, FATransition,
                                DdNode*, PDSTransition, Name);
extern void add_bdd_head (Head*, Head, DdNode*);
extern void merge_origins (OriginList, OriginList, OriginList*, DdNode**);
extern void get_names_from_state (Name,Name*,Name*);
extern Head get_head_from_state (Name);
extern void get_rid_of_the_bs (FATransTable*);
extern DdNode* compute_rep (Head, Head, char);

/* trace.c */
extern DdNode* find_one (DdNode*,int);
extern void find_one_init ();
extern int trace_findloop (Path*,Head,DdNode*,int,Path (*)(Path,Rule,DdNode*));
extern void get_post_trace (Head);
extern void get_pre_trace ();

extern Path find_conf (Head);
extern Path trace_step_back (Path);

extern DdNode* bp_find_one (DdNode*,int,Name);
extern void bp_make_tracemasks (bp_fun_t);
extern void bp_get_trace_newton (Path,char);
extern void bp_get_trace_xml (Path,char);

/* pa.c */
extern void print_post_automaton (FATransTable*);
extern void print_pre_automaton (FATransTable*);

#endif
