%{

#include <string.h>
#define YY_NO_UNPUT

const char *propstr;

%}

%option noyywrap

%%

"A"		{ return PR_FORALL; }
"E"		{ return PR_EXISTS; }

[A-Za-z_][A-Za-z0-9_]* {
			const_t con;
			proplval.name = name_create(proptext);
			for (con = constlist; con; con = con->next)
			{
				if (con->name != proplval.name) continue;
				proplval.integer = con->value;
				return PR_NUMBER;
			}
			for (con = quantlist; con; con = con->next)
			{
				if (con->name != proplval.name) continue;
				proplval.quant = con;
				return PR_QUANT;
			}
			return PR_IDENT;
		}

[0-9]+		{
			proplval.integer = atoi(proptext);
			return PR_NUMBER;
		}

"|"		{ return PR_OR; }
"&"		{ return PR_AND; }
"^"		{ return PR_XOR; }
"!"	 	{ return PR_NOT; }
"=="|"<=>"	{ return PR_EQV; }

"+"		{ return PR_PLUS; }
"*"		{ return PR_MULT; }
"-"		{ return PR_MINUS; }
"/"		{ return PR_DIV; }
"<<"		{ return PR_SHL; }

"<="		{ return PR_LE; }
"="		{ return PR_EQ; }
"!="		{ return PR_NE; }
">="		{ return PR_GE; }

[][<>,;\(\)]	{ return proptext[0]; }

.		;
\n		;

