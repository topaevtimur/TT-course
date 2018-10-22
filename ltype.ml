type lambda = 
	| Var of string 
	| Abs of string * lambda 
	| App of lambda * lambda
