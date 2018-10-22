call make1.bat
call make3.bat

ocamlc -o hw2_inference parser.cmo lexer.cmo hw1.cmo hw2_unify.cmo hw2_inference.mli hw2_inference.ml
