%{

#include <string.h>
#define YY_NO_UNPUT

const char *ltlstr;

%}

%option noyywrap

%%

"!"		{ return L_NOT; }
"||"		{ return L_OR; }
"&&"		{ return L_AND; }
"->"		{ return L_IMP; }
"<->"		{ return L_EQV; }

"\[\]"		{ return L_ALWAYS; }
"<>"		{ return L_EVENTUALLY; }

"G"		{ return L_ALWAYS; }
"F"		{ return L_EVENTUALLY; }
"U"		{ return L_UNTIL; }
"V"		{ return L_DUAL; }
"X"		{ return L_NEXT; }

"true"		{ return L_TRUE; }
"false"		{ return L_FALSE; }

[A-Za-z0-9_\+\.]+	{
			ltllval.string = ltltext;
			return L_IDENT;
		}

"\""[^ }\n]+"\"" {
			ltllval.string = ltltext;
			return L_IDENT;
		}

[()]		{ return *yytext; }

.		;
\n		;

