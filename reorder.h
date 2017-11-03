/* =========================================================================

	Variable orderings

   ====================================================================== */


#ifndef REORDER_H
#define REORDER_H

#include "variables.h"

extern void (*mc_reorderproc)();
extern block_t mc_maxblock;

extern void reorder_varbitcopy ();
extern void reorder_bitvarcopy ();
extern void reorder_varcopybit ();
extern void reorder_lgbitvarcopy ();
extern void reorder_lgvarbitcopy ();
extern void reorder_lgmixed ();
extern void reorder_byfunction ();

extern void bp_reorder_dep ();

extern void print_shuffle ();

#endif
