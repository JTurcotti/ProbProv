main: set.ml map.ml util.ml event_util.ml raw_expr.ml expr.ml refactor.ml context.ml expr_repr.ml context_repr.ml blame_prim.ml logger.ml typecheck.ml equations.ml layers.ml analyze.ml parser.ml lexer.ml main.ml
	ocamlc -g unix.cma $^ -o main
	cp main ../test/main
	rm parser.ml
	rm lexer.ml

parser.ml: parser.mly
	ocamlyacc parser.mly
	rm parser.mli

lexer.ml: lexer.mll parser.ml
	ocamllex lexer.mll

