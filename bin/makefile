main: set.ml map.ml util.ml event_util.ml raw_expr.ml expr.ml refactor.ml context.ml typecheck.ml equations.ml layers.ml blame_prim.ml analyze.ml parser.ml lexer.ml expr_repr.ml context_repr.ml main.ml main_repr.ml
	ocamlc -g set.ml map.ml util.ml event_util.ml raw_expr.ml expr.ml refactor.ml context.ml typecheck.ml equations.ml layers.ml blame_prim.ml analyze.ml parser.ml lexer.ml expr_repr.ml context_repr.ml main.ml main_repr.ml -o main
	rm parser.ml
	rm lexer.ml

parser.ml: parser.mly
	ocamlyacc parser.mly
	rm parser.mli

lexer.ml: lexer.mll parser.ml
	ocamllex lexer.mll

