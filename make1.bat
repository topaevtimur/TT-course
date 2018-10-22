ocamlc -c ltype.ml

ocamlyacc parser.mly
ocamllex -q lexer.mll

ocamlc -c parser.mli parser.ml lexer.ml

ocamlc -o hw1 parser.cmo lexer.cmo hw1.mli hw1.ml
