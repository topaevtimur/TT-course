open List
open Ltype
open Hw1
open Hw2_unify

type simp_type = | S_Elem of string | S_Arrow of simp_type * simp_type
type hm_lambda = | HM_Var of string | HM_Abs of string * hm_lambda | HM_App of hm_lambda * hm_lambda | HM_Let of string * hm_lambda * hm_lambda
type hm_type = | HM_Elem of string | HM_Arrow of hm_type * hm_type | HM_ForAll of string * hm_type

module String_Map = Map.Make(String);;



let id = ref 0;;



let new_name () = let name = "name" ^ (string_of_int (!id)) in id := !id + 1; name;;
let new_type () = let name = "typename" ^ (string_of_int (!id)) in id := !id + 1; Var name;;
let new_hm_type () = let name = "typename" ^ (string_of_int (!id)) in id := !id + 1; HM_Elem name;;

let rec get_system context expr goal equations = 
	match expr with
	| Ltype.Var x -> 
		(try (context, (let (_, e) = List.find (fun (t, e) -> t = x) context in e, goal) :: equations)
		with Not_found -> failwith "Not enough context")
	| Ltype.Abs (x, p) -> 
		let x_type = new_type () and p_type = new_type () in
		get_system ((x, x_type) :: context) p p_type ((goal, Fun ("fun", [x_type; p_type])) :: equations) 
	| Ltype.App (p, q) -> 
		let q_type = new_type () in let p_type = Fun ("fun", [q_type; goal]) in
		let (c1, e1) = (get_system context p p_type equations) and 
			(c2, e2) = (get_system context q q_type equations) in (c1 @ c2, e1 @ e2);;


let rec rmv_dps lst res = 
	match lst with
	| [] -> res
	| h :: tail -> if List.mem h res then rmv_dps tail res else rmv_dps tail (h :: res)
;;

let rec remove_dups lst = rmv_dps lst [];;

let build_system expr = 
	let (context, system) = get_system [] expr (new_type()) [] in 
	(remove_dups context, remove_dups system);;

let rec term_to_type term = 
	match term with
	| Var x -> S_Elem x
	| Fun (basic_fun_name, l :: r :: []) -> S_Arrow (term_to_type l, term_to_type r)
	| _ -> failwith "unexpected algebraic term"
;;


let rec term_to_type term = 
	match term with
	| Var x -> S_Elem x
	| Fun ("fun", l :: r :: []) -> S_Arrow (term_to_type l, term_to_type r)
	| _ -> failwith "unexpected algebraic term";;

let infer_simp_type expr = 
	id := 0; 
	let (context, sys) = build_system expr in
	match solve_system sys with
	| Some solution -> Some (
		List.map (fun (x, t) -> (x, term_to_type t)) 
			(List.map (fun (x, t) -> (x, apply_substitution solution t)) context), 
		let (_, tmp) = List.find (fun (x, t) -> x = "typename" ^ "0") solution in term_to_type tmp)
	| None -> None;;

let rec sub_vars expr vars = 
	match expr with
	| HM_Elem t -> (try String_Map.find t vars with Not_found -> expr)
	| HM_Arrow (t1, t2) -> HM_Arrow (sub_vars t1 vars, sub_vars t2 vars)
	| HM_ForAll (_, _) -> failwith "internal quantifier found"
;;

let rec rnm_vars expr vars = 
	match expr with
	| HM_ForAll (x, t) -> rnm_vars t (String_Map.add x (new_hm_type ()) vars)
	| _ -> sub_vars expr vars
;;

let sub_fresh_vars expr = rnm_vars expr String_Map.empty;;

let rec subst_to_hm_type subst t = 
	match t with
	| HM_Elem x -> (try let (v, e) = List.find (fun (var, expr) -> var = x) subst in e with Not_found -> t) 
	| HM_Arrow (t1, t2) -> HM_Arrow (subst_to_hm_type subst t1, subst_to_hm_type subst t2)
	| HM_ForAll (x, t1) -> HM_ForAll (x, subst_to_hm_type (List.filter (fun (v, e) -> v <> x) subst) t1)
;;

let subst_to_context subst context = 
	String_Map.map (fun t -> subst_to_hm_type subst t) context
;;

let rec get_fvs expr free except = 
	match expr with
	| HM_Elem x -> if not (List.mem x except || List.mem x free) then x :: free else free
	| HM_ForAll (x, p) -> get_fvs p free (x :: except)
	| HM_Arrow (p, q) -> (get_fvs p free except) @ (get_fvs q free except);;

let free_vars expr = get_fvs expr [] [];;


let rec abstract context t = 
	let free_vars_context context = 
		String_Map.fold (fun k v l -> (free_vars v) @ l) context [] in
	let fv_t = free_vars t and fv_c = free_vars_context context in 
		List.fold_left (fun t v -> if List.mem v fv_c then t else HM_ForAll (v, t)) t fv_t;;

exception NotTypeable;;

let rec alg_of_hm expr = 
	match expr with
	| HM_Elem x -> Var x
	| HM_Arrow (t1, t2) -> Fun ("arrow", [alg_of_hm t1; alg_of_hm t2])
	| HM_ForAll (x, t) -> Fun ("forall", [Var x; alg_of_hm t]);;

let rec hm_of_alg term = 
	match term with
	| Var x -> HM_Elem x
	| Fun (f, l :: r :: []) when f = "arrow" -> HM_Arrow (hm_of_alg l, hm_of_alg r)
	| Fun (f, Var x :: r :: []) when f = "forall" -> HM_ForAll (x, hm_of_alg r)
	| _ -> failwith "unexpected algebraic term";;

let rec infer_hm_type context expr =
	let rec compose subst_list = 
		let compose2 s1 s2 = 
		let substed = List.map (fun (x, t) -> (x, subst_to_hm_type s1 t)) s2 in
		let filtered = List.filter (fun (x1, t1) -> 
			(try let _ = List.find (fun (x2, t2) -> x1 = x2) s1 in false with Not_found -> true)) substed in 
			s1 @ filtered in
	match subst_list with 
	| [] -> []
	| h :: [] -> h
	| h :: tail -> compose2 h (compose tail) in
		match expr with
		| HM_Var x -> (try ([], sub_fresh_vars (String_Map.find x context)) with Not_found -> raise NotTypeable)
		| HM_App (e1, e2) -> 
			let (s1, t1) = infer_hm_type context e1 in 
			let (s2, t2) = infer_hm_type (subst_to_context s1 context) e2 and beta = new_hm_type () in 
			(match solve_system [(alg_of_hm (subst_to_hm_type s2 t1), alg_of_hm (HM_Arrow (t2, beta)))] with
			| Some v -> let s = List.map (fun (x, t) -> (x, hm_of_alg t)) v in (compose [s; s2; s1], subst_to_hm_type s beta)
			| None -> raise NotTypeable)
		| HM_Abs (x, e) -> 
			let beta = new_hm_type () in 
			let (s, t) = infer_hm_type (String_Map.add x beta context) e in 
			(s, HM_Arrow (subst_to_hm_type s beta, t))
		| HM_Let (x, e1, e2) -> 
			let (s1, t1) = infer_hm_type context e1 in let new_context = subst_to_context s1 context in
			let rec abstract context t =
				let free_vars_context context =	String_Map.fold (fun k v l -> (free_vars v) @ l) context []
				in let fv_t = free_vars t and fv_c = free_vars_context context in 
				List.fold_left (fun t v -> if List.mem v fv_c then t else HM_ForAll (v, t)) t fv_t
			in let (s2, t2) = infer_hm_type (String_Map.add x (abstract new_context t1) new_context) e2 in 
			(compose [s2; s1], t2);;



let sm_union m1 m2 = String_Map.fold (fun k v m -> String_Map.add k v m) m1 m2;;

let get_context expression = 
	let rec get_typed_fvs expr free except = 
	match expr with
	| HM_Var x -> if not (List.mem x except || String_Map.mem x free) then String_Map.add x (new_hm_type ()) free else free
	| HM_Abs (x, p) -> get_typed_fvs p free (x :: except)
	| HM_App (p, q) -> sm_union (get_typed_fvs p free except) (get_typed_fvs q free except)
	| HM_Let (x, p, q) -> sm_union (get_typed_fvs p free except) (get_typed_fvs q free (x :: except))
	in get_typed_fvs expression String_Map.empty [];;


let rename expression = 
	let rec real_rename expr vars = 
		match expr with
		| HM_Var x -> (try String_Map.find x vars with Not_found -> expr)
		| HM_Abs (x, p) -> let v = new_name () in HM_Abs (v, real_rename p (String_Map.add x (HM_Var v) vars))
		| HM_App (p, q) -> HM_App (real_rename p vars, real_rename q vars)
		| HM_Let (x, p, q) -> let v = new_name () in let vs = String_Map.add x (HM_Var v) vars in 
			HM_Let (v, real_rename p vs, real_rename q vs)
	in real_rename expression String_Map.empty;;

let algorithm_w expr = let e = rename expr in (try Some (infer_hm_type (get_context e) e) with NotTypeable -> None);;

let rec hmt_to_string hm = 
        match hm with 
                HM_Elem v -> v
                | HM_Arrow (lhs, rhs) -> "("^(hmt_to_string lhs)^"->"^(hmt_to_string rhs)^")"
				| HM_ForAll (var, rhs) -> "V "^var^"."^(hmt_to_string rhs);;

(* let test1 =  HM_Let("x", HM_Abs("x", HM_Var("x")), HM_Var("x"));;
let secondTest = HM_Let("sq", HM_Abs("f", HM_Abs("x", HM_App(HM_Var("f"), HM_App(HM_Var("f"), HM_Var("x"))))), HM_App(HM_Var("sq"), HM_App(HM_Var("sq"), HM_App(HM_Var("sq"), HM_App(HM_Var("sq"), HM_App(HM_Var("sq"), HM_App(HM_Var("sq"), HM_App(HM_Var("sq"), HM_App(HM_Var("sq"), HM_App(HM_Var("sq"), HM_App(HM_Var("sq"), HM_App(HM_Var("sq"), HM_App(HM_Var("sq"), HM_Var("sq"))))))))))))));;
match algorithm_w secondTest with 
	None -> print_string "NONE\n\n"
	| Some (ls, tp) -> 
		print_string "Ok\n";
		List.iter (fun (var, tp) -> print_string (var^":"^(hmt_to_string tp)^"\n")) ls;
		print_string ("type" ^ (hmt_to_string tp));;  *)