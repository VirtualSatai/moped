/* =========================================================================

	Just some sorting routines

   ====================================================================== */

#ifndef SORT_H
#define SORT_H


typedef struct bp_iwp_element *bp_iwp_t;

struct bp_iwp_element
{
	int i;
	void *p;
};

extern void sort_int (int*,int,int);
extern void sort_int_rev (int*,int,int);
extern void sort_iwp_rev (bp_iwp_t,int,int);

#endif
