/* =========================================================================

   Declare BDD-related variables.

   ====================================================================== */


#ifndef BDD_H
#define BDD_H

#include <stdio.h>
#define ARGS(protos) protos
#include <cudd.h>
#include "name.h"

extern DdManager *mc_mgr;
extern DdNode **bddvars;
extern DdNode **pvars, **qvars, **ppvars;
extern DdNode **yvars, **ypvars, **yppvars, **ypppvars;
extern DdNode **bvars;
extern DdNode *mc_cube1, *mc_cube2, *mc_cube3;
extern DdNode *mc_cube4, *mc_cube5, *mc_cube6;
extern DdNode *mc_cube7, *mc_cube8, *mc_cube9;
extern DdNode *mc_cube10, *fullset, *emptyset;
extern DdNode *mc_pyeqv, *mc_qyeqv, *mc_yyeqv;

extern int global_vars, local_vars;
extern int *mc_perm1, *mc_perm2, *mc_perm3, *mc_perm4;
extern int *mc_perm5, *mc_perm6, *mc_perm7, *mc_perm8;
extern int *mc_perm9, *mc_perm10, *mc_perm11, *mc_perm12;
extern int *mc_perm13, *mc_perm14;

extern int *global_var, *local_var;
extern int *mc_shuffle, *mc_rev_shuffle;

extern char mc_autoreorder;
extern unsigned char *bddval;

extern void init_cudd ();
extern void print_bdd (DdNode*,char**,int,int,int,int);

extern char *fatrans_set[], *rule_set[];
extern char *post_trans_set[];
extern char *post_set_init[], *post_set_mid[], *post_set_front[];
extern char *pre_set_all[], *pre_set_front[];

extern void check_refs (char*);
extern void bdd_qsort(int*,int,int);
extern void bdd_rev_qsort(int*,int,int);

#define GLOBALS (yvars - pvars)
#define LOCALS (bvars - yvars)

#endif
