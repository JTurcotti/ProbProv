srcs := set.ml map.ml util.ml event_util.ml colors.ml raw_expr.ml expr.ml  expr_repr.ml refactor.ml context.ml blame_prim.ml logger.ml typecheck.ml context_repr.ml equations.ml layers.ml analyze.ml parser.ml lexer.ml interference_paths.ml

main: $(srcs) io.ml main.ml
	ocamlc -g unix.cma $^ -o main
	cp main ../test/main
	rm parser.ml
	rm lexer.ml

flow_main: $(srcs) io.ml flow_main.ml
	ocamlc -g unix.cma $^ -o flow_main
	cp flow_main ../test/flow_main
	rm parser.ml
	rm lexer.ml

parser.ml: parser.mly
	ocamlyacc parser.mly
	rm parser.mli

lexer.ml: lexer.mll parser.ml
	ocamllex lexer.mll

clean:
	rm *.cmo
	rm *.cmi
	rm parser.ml
	rm lexer.ml

