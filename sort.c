#include "sort.h"

// fixme: replace these by heapsort and "pointerize" them

void sort_int (int *a, int left, int right)
{
	int eq,lo,hi,piv,tmp;

	if (left >= right) return;
	piv = a[right]; lo = eq = left; hi = right;
	while (lo <= hi)
	{
		if (a[hi] > piv) hi--;
		else
		{
			tmp = a[lo], a[lo] = a[hi], a[hi] = tmp;
			if (a[lo] < piv)
			{
				tmp = a[eq], a[eq] = a[lo], a[lo] = tmp;
				eq++;
			}
			lo++;
		}
	}
	sort_int(a,left,eq-1);
	sort_int(a,lo,right);
}

void sort_int_rev (int *a, int left, int right)
{
	int eq,lo,hi,piv,tmp;

	if (left >= right) return;
	piv = a[right]; lo = eq = left; hi = right;
	while (lo <= hi)
	{
		if (a[hi] < piv) hi--;
		else
		{
			tmp = a[lo], a[lo] = a[hi], a[hi] = tmp;
			if (a[lo] > piv)
			{
				tmp = a[eq], a[eq] = a[lo], a[lo] = tmp;
				eq++;
			}
			lo++;
		}
	}
	sort_int_rev(a,left,eq-1);
	sort_int_rev(a,lo,right);
}

void sort_iwp_rev (bp_iwp_t a, int left, int right)
{
	int eq,lo,hi,piv;
	struct bp_iwp_element tmp;

	if (left >= right) return;
	piv = a[right].i; lo = eq = left; hi = right;
	while (lo <= hi)
	{
		if (a[hi].i < piv) hi--;
		else
		{
			tmp = a[lo], a[lo] = a[hi], a[hi] = tmp;
			if (a[lo].i > piv)
			{
				tmp = a[eq], a[eq] = a[lo], a[lo] = tmp;
				eq++;
			}
			lo++;
		}
	}
	sort_iwp_rev(a,left,eq-1);
	sort_iwp_rev(a,lo,right);
}
