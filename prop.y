%{

#include <string.h>

#include "common.h"
#include "variables.h"
#include "ftree.h"

int proplex();
const_t quantlist;
extern const_t constlist;
FormulaTree proptree;
prop_t mc_properties;

extern void properror (char*);

%}

%union 
{
	int integer;
	Name name;
	FormulaTree etree;
	const_t quant;
}

%token <name> PR_IDENT
%token <integer> PR_NUMBER
%token <quant> PR_QUANT
%token PR_OR PR_AND PR_NOT
%token PR_EQV PR_XOR
%token PR_PLUS PR_MINUS
%token PR_MULT PR_DIV PR_SHL
%token PR_LE PR_EQ PR_NE PR_GE
%token PR_FORALL PR_EXISTS

%type <etree> expr intexpr
%type <etree> intterm
%type <etree> variable
%type <integer> comp_op

%right ')'
%left PR_EQV
%left PR_XOR
%left PR_OR
%left PR_AND
%right PR_NOT

%left PR_PLUS PR_MINUS
%left PR_MULT PR_DIV
%left PR_SHL

%%

start	: expr	{ proptree = $1; } ;

expr	: variable
	| intexpr
	| '(' expr ')'		{ $$ = $2; }
	| expr PR_OR expr	{ $$ = etree_create(E_OR,0,$1,$3); }
	| expr PR_AND expr	{ $$ = etree_create(E_AND,0,$1,$3); }
	| expr PR_EQV expr	{ $$ = etree_create(E_EQV,0,$1,$3); }
	| expr PR_XOR expr	{ $$ = etree_create(E_XOR,0,$1,$3); }
	| PR_NOT expr { $$ = etree_create(E_NOT,0,$2,NULL); }
	| PR_FORALL quant '(' intexpr ',' intexpr ')' expr
	  {
		quantlist->lower = (int)$4;
		quantlist->upper = (int)$6;
		$$ = etree_create(E_FORALL,(identref_t)quantlist,$8,NULL);
		quantlist = quantlist->next;
	  }
	| PR_EXISTS quant '(' intexpr ',' intexpr ')' expr
	  {
		quantlist->lower = (int)$4;
		quantlist->upper = (int)$6;
		$$ = etree_create(E_EXISTS,(identref_t)quantlist,$8,NULL);
		quantlist = quantlist->next;
	  } ;

quant	: PR_IDENT
	  {
		const_t q;
		q = common_malloc(sizeof(struct const_element));
		q->name = $1;
		q->next = quantlist;
		quantlist = q;
	  } ;

variable: PR_IDENT
	  {
		$$ = etree_create(E_IDENT,NULL,NULL,NULL);
		$$->ident = $1;
	  }
	| PR_IDENT '[' intterm ']'
	  {
		$$ = etree_create(E_IDENT,NULL,NULL,$3);
		$$->ident = $1;
	  } ;

intexpr	: intterm comp_op intterm
	  {
		$$ = etree_create(E_IEXPR,0,$1,$3);
		$$->ident = $2;
	  } ;

intterm	: intterm PR_PLUS intterm	{ $$ = etree_create(E_PLUS,0,$1,$3); }
	| intterm PR_MINUS intterm	{ $$ = etree_create(E_MINUS,0,$1,$3); }
	| intterm PR_MULT intterm	{ $$ = etree_create(E_MULT,0,$1,$3); }
	| intterm PR_DIV intterm	{ $$ = etree_create(E_DIV,0,$1,$3); }
	| intterm PR_SHL intterm	{ $$ = etree_create(E_SHL,0,$1,$3); }
	| variable
	| PR_QUANT { $$ = etree_create(E_QUANT,(identref_t)$1,NULL,NULL); }
	| PR_NUMBER { $$ = etree_create(E_NUMBER,(identref_t)$1,NULL,NULL); }
	;

comp_op	: '<'	  { $$ = E_LT; }
	| PR_LE  { $$ = E_LE; }
	| PR_EQ  { $$ = E_EQ; }
	| PR_NE  { $$ = E_NE; }
	| PR_GE  { $$ = E_GE; }
	| '>'	  { $$ = E_GT; }
	;

%%

#define YY_ALWAYS_INTERACTIVE 1
#include "proplex.c"

void properror (char *info)
{
	common_error("syntax error in property: %s",info);
}

void init_properties ()
{
	mc_properties = NULL;
}

void add_property (Name n)
{
	char *s = strdup(name_cstring(n));
	prop_t np;

	s[strlen(s)-1] = 0;
	quantlist = NULL;
	propstr = s+1;
        if (propparse())
                common_error("parse errors encountered in property");
	free(s);

	np = malloc(sizeof(struct prop_element));
	np->prop = n;
	np->tree = proptree;
	np->cond = NULL;
	np->next = mc_properties;
	mc_properties = np;
}
