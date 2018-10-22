call make1.bat

ocamlc -o hw1_reduction ltype.cmo parser.cmo lexer.cmo hw1.cmo hw1_reduction.mli hw1_reduction.ml
