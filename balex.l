%{

#include <string.h>
#define YY_NO_UNPUT

%}

%option noyywrap

%%

"/*"[^}\n]*"*/"   ;


"!"		{ return NOT; }
"||"		{ return OR; }
"&&"		{ return AND; }
"never"         { return NEVER; }
"goto"		{ return GOTO; }
"skip"		{ return SKIP; }
"if"		{ return IF; }
"fi"		{ return FI; }
"false"		{ return S_FALSE; }

[A-Za-z0-9_\+]+	{
			char *c, *var = strdup(batext);

			while ((c = strstr(var,"__colon__")))
			{
				char *nf = malloc(strlen(var)-7);
				*c = 0;
				sprintf(nf,"%s:%s",var,c+9);
				free(var);
				var = nf;
			}
			balval.string = var;
			return IDENT;
		}

->		{ return ARROW; }
[(){}:;]	{ return *yytext; }

.		;
\n		;

