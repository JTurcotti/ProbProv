srcs := set.ml map.ml util.ml event_util.ml colors.ml raw_expr.ml expr.ml  expr_repr.ml refactor.ml context.ml blame_prim.ml logger.ml context_repr.ml typecheck.ml equations.ml layers.ml analyze.ml parser.ml lexer.ml interference_paths.ml

all: main flow_main flow_check

main: $(srcs) io.ml main.ml
	ocamlc -g unix.cma $(srcs) io.ml main.ml -o main
	cp main ../test/main

flow_main: $(srcs) io.ml flow_main.ml
	ocamlc -g unix.cma $(srcs) io.ml flow_main.ml -o flow_main
	cp flow_main ../test/flow_main

flow_check: $(srcs) io.ml flow_check.ml
	ocamlc -g unix.cma $(srcs) io.ml flow_check.ml -o flow_check
	cp flow_check ../test/flow_check




parser.ml: parser.mly
	ocamlyacc parser.mly
	rm parser.mli

lexer.ml: lexer.mll parser.ml
	ocamllex lexer.mll

clean:
	rm *.cmo || true
	rm *.cmi || true
	rm *.cmt || true
	rm parser.ml || true
	rm lexer.ml || true

