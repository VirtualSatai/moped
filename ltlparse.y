%{

#include <stdio.h>
#include <stdlib.h>

#include "ftree.h"
#include "string.h"
#include "common.h"

int ltllex();
void ltlerror(char*);
Name ltl_create_prop_name();

FormulaTree ltl_tree;
NameTree ltl_nametree;

%}

%union 
{
	char        *string;
	FormulaTree  ftree;
}

%token <string> L_IDENT
%token L_NOT L_OR L_AND L_IMP L_EQV
%token L_ALWAYS L_EVENTUALLY
%token L_UNTIL L_DUAL L_NEXT
%token L_TRUE L_FALSE

%type <ftree> form

%left L_EQV
%left L_IMP
%right L_ALWAYS L_EVENTUALLY L_NEXT
%left L_UNTIL L_DUAL
%left L_OR
%left L_AND
%right L_NOT

%%

start	: form	{ ltl_tree = $1; } ;

form	: L_IDENT
	  {
		Name n_conv, n_orig = name_create($1);
		NameNode nn = name_tree_find(ltl_nametree,n_orig);

		if (!nn)
		{
			n_conv = ltl_create_prop_name();

			/* at this point parse the expression and
			   enter it into the nametree */

			name_tree_insert(&ltl_nametree,
				name_tree_mknode(n_orig,n_conv,NULL));
			name_tree_insert(&ltl_nametree,
				name_tree_mknode(n_conv,n_orig,NULL));
		}
		else
			n_conv = nn->refname;


		$$ = ftree_create(F_IDENT,n_conv,NULL,NULL);

	  }

	| L_TRUE		{ $$ = ftree_create(F_TRUE,0,NULL,NULL);  }
	| L_FALSE		{ $$ = ftree_create(F_FALSE,0,NULL,NULL); }
	| '(' form ')'		{ $$ = $2; }

	| L_NOT form		{ $$ = ftree_create(F_NOT,0,$2,NULL);	}
	| L_ALWAYS form		{ $$ = ftree_create(F_G,0,$2,NULL);	}
	| L_EVENTUALLY form	{ $$ = ftree_create(F_F,0,$2,NULL);	}
	| L_NEXT form		{ $$ = ftree_create(F_X,0,$2,NULL);	}

	| form L_UNTIL form	{ $$ = ftree_create(F_U,0,$1,$3);	}
	| form L_DUAL form	{ $$ = ftree_create(F_V,0,$1,$3);	}
	| form L_AND form	{ $$ = ftree_create(F_AND,0,$1,$3);	}
	| form L_OR form	{ $$ = ftree_create(F_OR,0,$1,$3);	}
	| form L_EQV form	{ $$ = ftree_create(F_EQV,0,$1,$3);	}
	| form L_IMP form	{ $$ = ftree_create(F_IMP,0,$1,$3);	}
	;

%%

#define YY_ALWAYS_INTERACTIVE 1
#include "ltllex.c"

void ltlerror (char *info)
{ 
	common_error("syntax error in formula: %s", info);
}

Name ltl_create_prop_name ()
{
	static int propnr = 0;
	int n = propnr++;

	common_strbuf_new();
	common_addbuf("prop");

	do {
		common_addbuf("%c",'a'+(n%26));
		n /= 26;
	} while (n);

	return name_create(common_strbuf);
}

void ltl_printform (FormulaTree tree)
{
	char *op = NULL;

	switch (tree->token)
	{
	    case F_FALSE:
		common_addbuf("false"); return;
	    case F_TRUE:
		common_addbuf("true"); return;
	    case F_NOT:	if (!op) op = "!";
	    case F_F:	if (!op) op = "<>";
	    case F_G:	if (!op) op = "[]";
	    case F_X:	if (!op) op = "X";
		common_addbuf(op);
		common_addbuf("(");
		ltl_printform(tree->left);
		common_addbuf(")");
		return;
	    case F_AND:	if (!op) op = "&&";
	    case F_OR:	if (!op) op = "||";
	    case F_IMP:	if (!op) op = "->";
	    case F_EQV:	if (!op) op = "<->";
	    case F_U:	if (!op) op = " U ";
	    case F_V:	if (!op) op = " V ";
		common_addbuf("(");
		ltl_printform(tree->left);
		common_addbuf(op);
		ltl_printform(tree->right);
		common_addbuf(")");
		return;
	    case F_IDENT:
		common_addbuf(name_cstring(tree->ident));
		return;
	    default:
		common_error("unknown token (%i)",tree->token);
		return;
	}
}

char* build_formula (char *formula)
{
	ltl_nametree = NULL;
	ltlstr = formula;
	ltlparse();

	common_strbuf_new();
	ltl_printform(ltl_tree);
	ftree_delete(ltl_tree);
	return common_strbuf;
}
