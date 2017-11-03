%{

#include <stdio.h>
#include <stdlib.h>

#include "ba.h"
#include "ftree.h"
#include "string.h"
#include "common.h"
#include "netconv.h"
#include "mcheck.h"

int balex();
void baerror(char*);
extern char* build_formula (char*);
extern NameTree ltl_nametree;

extern void init_properties();
extern void add_property(Name);

BuechiAutomaton mc_ba;
NameSet actstates = NULL;
NameTree ba_nametree;
Name ba_cstate;

%}

%union 
{
	char        *string;
	FormulaTree  ftree;
	int	     state;
}

%token <string> IDENT
%token COLON SEMICOLON
%token IF FI
%token BOPEN BCLOSE
%token B2OPEN B2CLOSE
%token ARROW GOTO SKIP NEVER
%token NOT OR AND S_FALSE

%type  <ftree> formula
%type  <state> statename

%left OR
%left AND
%left NOT

%%

automaton
	: NEVER '{' statelist '}' ;

statelist
	:
	| state statelist ;

state	: statenamelist namebrk ifclause 
	| statenamelist namebrk skipstatement ;

statenamelist
	: statenamelist statename
	  {  name_set_insert(&actstates,$2);  }
	| statename		  
	  {  name_set_insert(&actstates,$1);  } ;
	
statename
	: IDENT ':'
	  {
		$$ = name_create($1); free($1);
		if (!mc_ba.start_state) mc_ba.start_state = $$;
	  } ;

namebrk	: {
		NameSet tmp;

		ba_cstate = actstates->name;
		for (tmp = actstates; tmp; tmp = tmp->next)
			if (ba_is_finalstate(tmp->name)) ba_cstate = tmp->name;

		for (tmp = actstates; tmp; tmp = tmp->next)
			name_tree_insert(&ba_nametree,
				name_tree_mknode(tmp->name,ba_cstate,NULL));
		name_set_delete(&actstates);
	  } ;

skipstatement
	: SKIP
	  {
		FormulaTree skip = ftree_create(F_TRUE,0,NULL,NULL);
		ba_insert_trans(&mc_ba,ba_cstate,skip,ba_cstate);
	  } ;

ifclause: IF conditionlist FI ';' ;

conditionlist
	:
	| condition conditionlist ;

condition
	: ':' ':' formula ARROW GOTO IDENT
	  {
		Name goal = name_create($6);
		ba_insert_trans(&mc_ba,ba_cstate,$3,goal);
		free($6);
	  }
	| ':' ':' S_FALSE ;

formula	: IDENT
	  {
		if (!strcmp($1,"0"))
			$$ = ftree_create(F_FALSE,0,NULL,NULL);
		else if (!strcmp($1,"1"))
			$$ = ftree_create(F_TRUE,0,NULL,NULL);
		else
		{
			Name n_conv = name_create($1);
			if (mc_use_ba)
			{
			    $$ = ftree_create(F_IDENT,n_conv,NULL,NULL);
			}
			else
			{
			    NameNode nn = name_tree_find(ltl_nametree,n_conv);
			    $$ = ftree_create(F_IDENT,nn->refname,NULL,NULL);	
			}
		}
		free($1);
	  }
	| NOT formula		{ $$ = ftree_create(F_NOT,0,$2,NULL); }
	| formula OR formula	{ $$ = ftree_create(F_OR,0,$1,$3);    }
	| formula AND formula	{ $$ = ftree_create(F_AND,0,$1,$3);   }
	| '(' formula ')'	{ $$ = $2; } ;

%%

#include "balex.c"

void baerror (char *info)
{ 
	common_error("syntax error in Buechi automaton: %s", info);
}

void build_ba (char *formula)
{
	char *tmpbuf = common_malloc(L_tmpnam);
	char *tmp, *cform;
	int i;

	if (mc_use_ba)
	{
		strcpy(tmpbuf,formula);
	}
	else
	{
		cform = build_formula(formula);
		tmp = malloc(32 + strlen(cform) + L_tmpnam);
		sprintf(tmp,"-f '!(%s)' > %s",cform, tmpnam(tmpbuf));
		nc_run_spin(tmp);
		free(tmp);
	}

	if (!(bain = fopen(tmpbuf,"r")))
		common_error("cannot open file %s",tmpbuf);
	mc_ba = ba_empty();
	ba_nametree = NULL;
	baparse();
	fclose(bain);

	init_properties();
	if (!mc_use_ba)
	{
		remove(tmpbuf);

		for (i = 0; i < ltl_nametree->used; i++)
		{
			char *s = name_cstring(ltl_nametree->data[i]->name);
			if (*s != '"') continue;
			add_property(ltl_nametree->data[i]->name);
		}

		name_tree_delete(&ltl_nametree);
	}

	common_free(tmpbuf,L_tmpnam);

	ba_canonicize(&mc_ba);
	name_tree_delete(&ba_nametree);
	ba_minimize(&mc_ba);
}
