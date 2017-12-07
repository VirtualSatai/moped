%{

#include <string.h>

#include "pds.h"
#include "common.h"
#include "variables.h"
#include "reorder.h"
#include "ftree.h"
#include "expr.h"

extern int pdslineno;
int pds_p1, pds_y1, pds_p2, pds_y2, pds_y3;
int pp_current_label;
int pdslex();

void pdserror (char*);

extern PushdownSystem mc_pds;
extern int mc_verbose;
extern int mc_restrict;
extern NameTreeList mc_atoms;

%}

%union 
{
	char *string;
	int integer;
	NameStack stack;
	NameSet set;
	Name name;
	DdNode *bdd;
	DdNode **varptr;
	ident_t ident;
	identref_t identref;
	FormulaTree etree;
	block_t block;
	const_t quant;
}

%token <string> LABEL
%token <name> IDENT
%token <integer> NUMBER
%token <quant> QUANT
%token PDS_OR PDS_AND PDS_NOT
%token PDS_EQV PDS_XOR
%token PDS_PLUS PDS_MINUS
%token PDS_MULT PDS_DIV PDS_SHL
%token PDS_LE PDS_EQ PDS_NE PDS_GE
%token PDS_FORALL PDS_EXISTS
%token ARROW PRIME
%token GLOBAL LOCAL BOOL INT
%token DEFINE
%token ATOMS

%type <stack> stacklist
%type <ident> globals varlist decl
%type <ident> boollist boolident
%type <ident> intlist intident
%type <ident> optdim
%type <name> optproc
%type <block> locals
%type <set> symblist symbols
%type <string> label
%type <name> startident stackident
%type <bdd> expression
%type <etree> expr intexpr boolvar
%type <etree> intterm indexvar
%type <name> varident
%type <identref> variable
%type <integer> comp_op
%type <integer> constexp

%right ')'
%left PDS_EQV
%left PDS_XOR
%left PDS_OR
%left PDS_AND
%right PDS_NOT

%left PDS_PLUS PDS_MINUS
%left PDS_MULT PDS_DIV
%left PDS_SHL

%%

automaton: defines vardecl startconfig atoms transitionlist ;

defines	: defines DEFINE IDENT constexp
	  {
		const_t con = common_malloc(sizeof(struct const_element));
		con->name = $3;
		con->value = $4;
		con->next = constlist;
		constlist = con;
	  }
	| defines DEFINE NUMBER constexp
	| ;

vardecl	: globals locals
	  {
		block_t tmp;
		mc_blocks = common_malloc(sizeof(struct block_element));
		mc_blocks->procname = 0;
		mc_blocks->names = NULL;
		mc_blocks->idents = $1;
		mc_blocks->next = mc_maxblock = tmp = $2;

		global_vars = $1? $1->index + ($1->type? $1->type : 1)
					    * ($1->dim? $1->dim : 1) : 0;
		local_vars = 0;
		while (tmp)
		{
			ident_t id = tmp->idents;
			int x = id? id->index + (id->type? id->type : 1)
						* (id->dim? id->dim : 1) : 0;
			if (x>local_vars) { mc_maxblock = tmp; local_vars = x; }
			tmp = tmp->next;
		}

		for (tmp = mc_blocks; tmp; tmp = tmp->next)
		{
			ident_t id = tmp->idents, nl = NULL, tmpid;
			
			while (id)
			{
				tmpid = id->next;
				id->next = nl;
				nl = id;
				id = tmpid;
			}
			tmp->idents = nl;
		}

		pds_p1 = pds_y1 = pds_p2 = pds_y2 = pds_y3 = 0;
		idchain = NULL;
		init_cudd();

		for (tmp = mc_blocks; tmp; tmp = tmp->next)
			build_properties(tmp);
	  } ;

globals	: GLOBAL varlist { $$ = $2;   }
	|		 { $$ = NULL; } ;

locals	: { $$ = NULL; local_vars = 0; }
	| locals LOCAL optproc symblist varlist
	  {
		NameSet set;
		$$ = common_malloc(sizeof(struct block_element));
		$$->procname = $3;
		$$->names = $4;
		$$->idents = $5;
		$$->next = $1;
		for (set = $$->names; set; set = set->next)
			name_tree_insert(&mc_localtree,
				name_tree_mknode(set->name,0,$$));
		local_vars = 0;
	  } ;

optproc	: IDENT
	| { $$ = 0; } ;

symblist: '(' symbols ')'
	  { $$ = $2; } ;

symbols	: IDENT
	  {
		NameSet set = NULL;
		name_set_insert(&set,$1);
		$$ = set;
	  }
	| symbols ',' IDENT
	  {
		name_set_insert(&$1,$3);
		$$ = $1;
	  } ;

varlist	: decl
	| varlist decl 
	  {
		$$ = $2;
		while ($2->next) $2 = $2->next;
		$2->next = $1;
	  } ;

decl	: BOOL boollist ';'	{ $$ = $2; }
	| INT intlist ';'	{ $$ = $2; }  ;

boollist: boolident		  { ($$ = $1)->next = NULL; }
	| boollist ',' boolident  { ($$ = $3)->next = $1; } ;

boolident: IDENT optdim
	   {
		$$ = $2;
		$$->varname = $1;
		$$->type = 0;
		$$->index = local_vars;
		local_vars += $$->dim? $$->dim : 1;
	   } ;

intident: IDENT optdim '(' constexp ')'
	  {
		$$ = $2;
		$$->varname = $1;
		if ($4 <= 0) pdserror("positive integer expected");
		$$->index = local_vars;
		local_vars += ($$->type = $4) * ($$->dim? $$->dim : 1);
	  } ;

optdim	: {
		($$ = common_malloc(sizeof(struct ident_element)))->dim = 0; 
	  }
	| '[' constexp ']'
	  {
		if ($2 <= 0) pdserror("positive integer expected");
		$$ = common_malloc(sizeof(struct ident_element));
		$$->dim = $2; $$->lo = 0; $$->hi = $2-1;
	  }
	| '[' constexp ',' constexp ']'
	  {
		if ($2 < 0) pdserror("nonnegative integer expected");
		$$ = common_malloc(sizeof(struct ident_element));
		$$->dim = $4-$2+1; $$->lo = $2; $$->hi = $4;
	  } ;

intlist : intident		{ ($$ = $1)->next = NULL; }
	| intlist ',' intident	{ ($$ = $3)->next = $1; } ;


startconfig
	: '(' startstate '<' stacklist '>' ')'
	  {
		mc_pds.start_stack = $4;
	  } ;

startstate
	: startident
	  {
		mc_pds.start_state = $1;
		mc_pds.start_bdd = fullset;
	  }
	| startident '(' expression ')'
	  {
		mc_pds.start_state = $1;
		mc_pds.start_bdd = $3;
	  } ;

startident: IDENT
	    {
		pds_p1 = $$ = $1;
		pds_y1 = pds_p2 = pds_y2 = pds_y3 = 0;
	    } ;

stackident: IDENT
	    {
		pds_y1 = $$ = $1;
		pds_p1 = pds_p2 = pds_y2 = pds_y3 = 0;
	    } ;

stacklist
	: stackident
	  {
		$$ = name_stack_empty();
		name_stack_push(&$$,$1,fullset);
	  }
	| stackident '(' expression ')'
	  {
		$$ = name_stack_empty();
		name_stack_push(&$$,$1,$3);
	  } ;

atoms	:
	| atoms atom ;

atom	: ATOMS IDENT { pp_current_label = $2; } proplist ;

proplist: propident
	| proplist ',' propident ;

propident: IDENT
	{
		int propos = $1;
		NameTreeList tmp = mc_atoms;

		while (tmp)
		{
			if (tmp->name == propos) break;
			tmp = tmp->next;
		}
		if (!tmp)
		{
			tmp = common_malloc(sizeof(struct NameTreeListStruct));
			tmp->name = propos;
			tmp->tree = NULL;
			tmp->next = mc_atoms;
			mc_atoms = tmp;
		}
		name_bal_insert(&(tmp->tree),pp_current_label);
	}

transitionlist:
	| transitionlist transition ;

transition
	: simp_trans_wrap label
	  {
		pds_insert_trans(&mc_pds, pds_p1, pds_y1, pds_p2, pds_y2,
					  pds_y3, fullset, $2, 0);
		if ($2) free($2);
	  }
	| simp_trans_wrap label '(' expression ')'
	  {
		pds_insert_trans(&mc_pds, pds_p1, pds_y1, pds_p2, pds_y2,
					  pds_y3, $4, $2, 0);
		Cudd_RecursiveDeref(mc_mgr,$4);
		if ($2) free($2);
	  } ;

simp_trans_wrap
	: simple_transition
	  {
		if (mc_verbose > 1) fprintf(stdout,"-## %s %s %s %s %s\n",
			name_cstring(pds_p1),name_cstring(pds_y1),
			name_cstring(pds_p2),name_cstring(pds_y2),
			name_cstring(pds_y3));
	  } ;

simple_transition
	: IDENT '<' IDENT '>' ARROW IDENT '<' IDENT IDENT '>'
	  { 
		pds_p1 = $1; pds_y1 = $3;
		pds_p2 = $6; pds_y2 = $8;
		pds_y3 = $9;
	  }
	| IDENT '<' IDENT '>' ARROW IDENT '<' IDENT '>'
	  {
		pds_p1 = $1; pds_y1 = $3;
		pds_p2 = $6; pds_y2 = $8; pds_y3 = 0;
	  }
	| IDENT '<' IDENT '>' ARROW IDENT '<' '>'
	  { 
		pds_p1 = $1; pds_y1 = $3;
		pds_p2 = $6; pds_y2 = pds_y3 = 0;
	  } ;

label	: { $$ = NULL; }
	| LABEL ;

expr	: boolvar
	| intexpr
	| '(' expr ')'		{ $$ = $2; }
	| expr PDS_OR expr	{ $$ = etree_create(E_OR,0,$1,$3); }
	| expr PDS_AND expr	{ $$ = etree_create(E_AND,0,$1,$3); }
	| expr PDS_EQV expr	{ $$ = etree_create(E_EQV,0,$1,$3); }
	| expr PDS_XOR expr	{ $$ = etree_create(E_XOR,0,$1,$3); }
	| PDS_NOT expr { $$ = etree_create(E_NOT,0,$2,NULL); }
	| PDS_FORALL quant '(' constexp ',' constexp ')' expr
	  {
		quantlist->lower = $4;
		quantlist->upper = $6;
		$$ = etree_create(E_FORALL,(identref_t)quantlist,$8,NULL);
		quantlist = quantlist->next;
	  }
	| PDS_EXISTS quant '(' constexp ',' constexp ')' expr
	  {
		quantlist->lower = $4;
		quantlist->upper = $6;
		$$ = etree_create(E_EXISTS,(identref_t)quantlist,$8,NULL);
		quantlist = quantlist->next;
	  } ;

quant	: IDENT
	  {
		const_t q;
		q = common_malloc(sizeof(struct const_element));
		q->name = $1;
		q->next = quantlist;
		quantlist = q;
	  } ;

expression: expr
	  {
		$$ = build_expr($1);
		free_expr_tree($1);
	  } ;

boolvar	: variable
	  {
		if ($1->ident->type) pdserror("boolean variable expected");
		if ($1->ident->dim) pdserror("missing subscript");
		$$ = etree_create(E_BVAR,$1,NULL,NULL);
	  }
	| indexvar
	  {
		if ($1->idref->ident->type)
			pdserror("boolean variable expected");
		$$ = $1;
		$1->token = E_BVAR;
		$1->left = (FormulaTree) idchain;
		idchain = NULL;
	  } ;

indexvar: variable '[' intterm ']'
	  {
		if (!$1->ident->dim) pdserror("unexpected subscript");
		$$ = etree_create(0,$1,NULL,$3);
	  } ;

intexpr	: intterm comp_op intterm
	  {
		FormulaTree tree = etree_create($2,0,$1,$3);
		$$ = etree_create(E_IEXPR,0,idchain,tree);
		idchain = NULL;
	  } ;

intterm	: intterm PDS_PLUS intterm	{ $$ = etree_create(E_PLUS,0,$1,$3); }
	| intterm PDS_MINUS intterm	{ $$ = etree_create(E_MINUS,0,$1,$3); }
	| intterm PDS_MULT intterm	{ $$ = etree_create(E_MULT,0,$1,$3); }
	| intterm PDS_DIV intterm	{ $$ = etree_create(E_DIV,0,$1,$3); }
	| intterm PDS_SHL intterm	{ $$ = etree_create(E_SHL,0,$1,$3); }
	| variable
	  {
		if (!$1->ident->type) pdserror("integer variable expected");
		$1 = add_to_idchain($1);
		$$ = etree_create(E_IDENT,$1,NULL,NULL);
		if ($1->ident->dim) pdserror("missing subscript");
	  }
	| indexvar
	  {
		if (!$1->idref->ident->type)
			pdserror("integer variable expected");
		$$ = $1;
		$$->token = E_IDENT;
		$1->idref->sub = $1->right;
		$1->idref->next = idchain;
		idchain = $1->idref;
		$1->right = NULL;
	  }
	| QUANT	 { $$ = etree_create(E_QUANT,(identref_t)$1,NULL,NULL); }
	| NUMBER { $$ = etree_create(E_NUMBER,(identref_t)$1,NULL,NULL); }
	| '{' intterm '}' { $$ = $2; } ;

comp_op	: '<'	  { $$ = E_LT; }
	| PDS_LE  { $$ = E_LE; }
	| PDS_EQ  { $$ = E_EQ; }
	| PDS_NE  { $$ = E_NE; }
	| PDS_GE  { $$ = E_GE; }
	| '>'	  { $$ = E_GT; } ;

variable: varident			/* (x,y) -> (p',y') */
	  {				/* in init cfg: (x,y) -> (p,y) */
		if (pds_p1 * pds_y1 == 0)
		    $$ = find_ident(pds_y1, $1, pds_p1? pvars : NULL, yvars);
		else
		    $$ = find_ident(pds_y1, $1, ppvars, ypvars);
		if (!$$) pdserror("invalid identifier");
	  }
	| varident PRIME		/* (x',y') -> (p,y) */
	  {
		if (pds_p1 * pds_y1 == 0) pdserror("invalid identifier");
		$$ = find_ident(pds_y2, $1, pvars, yvars);
		if (!$$) pdserror("invalid identifier");
	  }
	| varident PRIME PRIME		/*   (y'') -> (y'') */
	  {
		$$ = find_ident(mc_restrict? 0 : pds_y3, $1, NULL, yppvars);
		if (!$$) pdserror("invalid identifier");
	  } ;

varident: IDENT ;

constexp: constexp PDS_PLUS constexp	{ $$ = $1 + $3; }
	| constexp PDS_MINUS constexp	{ $$ = $1 - $3; }
	| constexp PDS_MULT constexp	{ $$ = $1 * $3; }
	| constexp PDS_DIV constexp	{ $$ = $1 / $3; }
	| constexp PDS_SHL constexp	{ $$ = $1 << $3; }
	| '(' constexp ')'		{ $$ = $2; }
	| NUMBER			{ $$ = $1; } ;

%%

#include "pdslex.c"

void pdserror (char *info)
{ 
	common_error("syntax error in pushdown system: %s, line %d",
			info,pdslineno);
}

void parse_pds (char *filename)
{
	mc_pds = pds_empty();
	quantlist = NULL;
	mc_localtree = NULL;
	mc_atoms = NULL;

	if (!(pdsin = fopen(filename,"r")))
		common_error("modelfile %s not found", filename);

	if (pdsparse())
		common_error("parse errors encountered while reading pds");

	fclose(pdsin);
}
