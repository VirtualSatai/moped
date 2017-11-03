%{

#include <string.h>
#define YY_NO_UNPUT

%}

%option noyywrap

%%

"global"	{ return GLOBAL; }
"local"		{ return LOCAL; }
"bool"		{ return BOOL; }
"int"		{ return INT; }
"define"	{ return DEFINE; }
"atoms"		{ return ATOMS; }
"A"		{ return PDS_FORALL; }
"E"		{ return PDS_EXISTS; }

[A-Za-z_][A-Za-z0-9_\.]* {
			const_t con;
			pdslval.name = name_create(pdstext);
			for (con = constlist; con; con = con->next)
			{
				if (con->name != pdslval.name) continue;
				pdslval.integer = con->value;
				return NUMBER;
			}
			for (con = quantlist; con; con = con->next)
			{
				if (con->name != pdslval.name) continue;
				pdslval.quant = con;
				return QUANT;
			}
			return IDENT;
		}

[0-9]+		{
			pdslval.integer = atoi(pdstext);
			return NUMBER;
		}

\"[^"]*\"	{
			pdslval.string = strdup(pdstext+1);
			pdslval.string[strlen(pdstext)-2] = 0;
			return LABEL;
		}


-->		{ return ARROW; }
"'"		{ return PRIME; }

"|"		{ return PDS_OR; }
"&"		{ return PDS_AND; }
"^"		{ return PDS_XOR; }
"!"	 	{ return PDS_NOT; }
"=="|"<=>"	{ return PDS_EQV; }

"+"		{ return PDS_PLUS; }
"*"		{ return PDS_MULT; }
"-"		{ return PDS_MINUS; }
"/"		{ return PDS_DIV; }
"<<"		{ return PDS_SHL; }

"<="		{ return PDS_LE; }
"="		{ return PDS_EQ; }
"!="		{ return PDS_NE; }
">="		{ return PDS_GE; }

[][<>,;\(\)]	{ return pdstext[0]; }

[{}\%#](.)*\n	{ pdslineno++; }
[ 	]	;
\n		{ pdslineno++; }

