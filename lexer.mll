{
	open Parser
}

rule token = parse
	| "\\" [' ']* 						{ LAMBDA }
	| ['a'-'z']+ ['0'-'9']* as name		{ VAR name }
	| '(' [' ']* 						{ OPAREN }
	| [' ']* ')'						{ CPAREN }
	| [' ']* '.' [' ']*					{ DOT }
	| [' ']+							{ WS }
	| eof								{ EOF }