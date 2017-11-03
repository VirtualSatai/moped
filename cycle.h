/* =========================================================================

	Declarations for cycle detection

   ====================================================================== */


#ifndef CYCLE_H
#define CYCLE_H

typedef struct CNodeStruct *CNode;
typedef struct CEdgeStruct *CEdge;

#include "bdd.h"
#include "heads.h"

struct CNodeStruct
{
	Head head;
	CEdge bkedges;
	CEdge fwedges;
	DdNode *z, *y, *x, *w;
	CNode next, stack;
	char flag;
};

struct CEdgeStruct
{
	CNode from, to;
	CEdge nextfrom, nextto;
	char b;
	DdNode *e;
};

#define create_cnode() (malloc(sizeof(struct CNodeStruct)))
#define create_cedge() (malloc(sizeof(struct CEdgeStruct)))

extern int mc_verbose, mc_poststar, mc_demand, mc_bp;
extern char (*mc_cyclemethod)(CNode);
extern Head (*mc_edgemethod)(Head*);

/* graph.c */
extern void dfs_search (Head);
extern void find_cover (Head);

/* closure.c */
void init_y_stack (CNode,CNode*);
void add_y_edge (CNode,DdNode*,CNode*);
void clear_y_stack (CNode);
extern char compute_closure (CNode);

/* xb.c */
extern char xb_decomp (CNode);

/* el.c */
extern char el_method (CNode);
extern char owcty_method (CNode);
extern void check_for_real_cycles (CNode,CNode);

/* elim.c */
extern void eliminate_stuff (CNode);

/* cycle.c */
extern Head find_cycles ();
extern Head find_summary (Head*);
extern Head find_direct (Head*);

#endif
