open List;;
open String;;
open Ltype;;

type peano = Z | S of peano;;

exception Neg_num;;

let rec peano_of_int x = 
	match x with
	| 0 -> Z
	| _ -> S (peano_of_int (x - 1));;

let rec int_of_peano p = 
	match p with
	| Z -> 0
	| S x -> 1 + int_of_peano x;;

let inc x = S x;;

let rec add x y = 
	match y with
	| Z -> x
	| S y1 -> S (add x y1);;

let rec sub x y = 
	match (x, y) with
	| (x, Z) -> x
	| (Z, y) -> raise Neg_num
	| (S xx, S yy) -> (sub xx yy);;

let rec mul x y = 
	match y with
	| Z -> Z
	| S y1 -> add (mul x y1) x;;

let rec power x y = 
	match y with
	| Z -> S Z
	| S y1 -> mul (power x y1) x;;


let rec reverse x y =
	match x with
	| [] -> y
	| head::tail -> reverse tail (head::y);;

let rev x = reverse x [];;

let rec take n l =
  if n <= 0 then [] else
    match l with
    | [] -> []
    | h :: tl -> h :: take (n - 1) tl

let rec drop n l =
  if n <= 0 then l else
    match l with
    | [] -> []
    | _ :: tl -> drop (n - 1) tl

let rec length l =
  match l with
  | [] -> 0
  | _::t -> 1 + length t

let rec merge_sort l =
  let rec merge x y =
    match x, y with
    | [], y -> y
    | x, [] -> x
    | hx :: tlx, hy :: tly ->
      if hx < hy
      then hx :: merge tlx (hy :: tly)
      else hy :: merge (hx :: tlx) tly
  in
  match l with
  | [] -> []
  | [x] -> [x]
  | _ ->
    let left = take (length l / 2) l in
    let right = drop (length l / 2) l in
    merge (merge_sort left) (merge_sort right)


let rec string_of_lambda x = 
	match x with
	| Var v -> v
	| App (l1, l2) -> "(" ^ string_of_lambda l1 ^ " " ^ string_of_lambda l2 ^ ")"
	| Abs (s, l) -> "(\\" ^ s ^ "." ^ string_of_lambda l ^ ")";;

let lambda_of_string x = Parser.main Lexer.token (Lexing.from_string (String.trim x));;
