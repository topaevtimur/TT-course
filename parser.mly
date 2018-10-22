%token <string> VAR
%token LAMBDA
%token DOT
%token WS
%token OPAREN CPAREN
%token EOF

%nonassoc DOT
%left WS

%start main
%type <Ltype.lambda> main
%%

main:
	| parse EOF	{ $1 }
;

parse:
	| OPAREN parse CPAREN 	{ $2 }
	| VAR					{ Ltype.Var $1 }
	| parse WS parse	  	{ Ltype.App ($1, $3) }
	| LAMBDA VAR DOT parse  { Ltype.Abs ($2, $4) }
;