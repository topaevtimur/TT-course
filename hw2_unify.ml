open List

type algebraic_term = Var of string | Fun of string * (algebraic_term list)


let rec get_fresh_name sys =
	let rec get_name term = 
		match term with
		| Var x -> x
		| Fun (f, args) -> f ^ (List.fold_left (^) "" (List.map get_name args))
	in let names = List.map (fun (l, r) -> get_name l ^ get_name r) sys in
	"x" ^ (List.fold_left (^) "" names)
;;

let system_to_equation system = 
	let name = get_fresh_name system and (lhs, rhs) = List.split system in 
	(Fun (name, lhs), Fun (name, rhs))
;;

let rec apply_substitution rules term = 
	match term with
	| Var x -> 
		(try let (v, e) = List.find (fun (var, expr) -> var = x) rules in e 
		with Not_found -> term)
	| Fun (f, args) -> Fun (f, List.map (fun arg -> apply_substitution rules arg) args)
;;

let rec equals t1 t2 = 
	match (t1, t2) with
	| (Var x, Var y) -> x = y
	| (Fun (f, args1), Fun (g, args2)) -> f = g && List.for_all2 equals args1 args2
	| _ -> false
;;

let rec check_solution subst system = 
	List.for_all 
		(fun (l, r) -> equals (apply_substitution subst l) (apply_substitution subst r)) 
		system
;;

let rec solve_system system = 
	let exception Err in
	let rec unify future past = 
	match future with
	| [] -> List.map (fun (l, r) -> match (l, r) with 
				| (Var x, _) -> (x, r) 
				| _ -> failwith "Something went wrong"
			) past
	| (l, r) :: tail -> if equals l r then unify tail past else	match (l, r) with
		| (Var x, _) ->
			let rec used var expr = match expr with
					| Var x -> x = var
					| Fun (f, args) -> List.exists (used var) args
			in if used x r then raise Err else
			let mapping = fun (a, b) -> (apply_substitution [(x, r)] a, apply_substitution [(x, r)] b) in
			unify (List.map mapping future) ((l, r) :: (List.map mapping past))
		| (Fun (_, _), Var _) -> unify ((r, l) :: tail) past
		| (Fun (f, a1), Fun (g, a2)) -> 
			if f = g then (try let decomposed = List.combine a1 a2 in unify (decomposed @ tail) past
				with Invalid_argument msg -> raise Err)
			else raise Err
 	in (try Some (unify system []) with Err -> None);;
