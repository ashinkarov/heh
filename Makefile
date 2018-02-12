OCB := ocamlbuild -j 8 -use-ocamlfind

SRC := ast.ml \
       value.ml \
       valueops.ml \
       main.ml \
       loc.ml \
       lexer.mll \
       parser.ml \
       ordinals.ml \
       storage.ml \
       env.ml \
       eval.ml \
       globals.ml \
       traverse.ml \
       traversal.ml \
       lifting.ml \
       compile_sac.ml \
       print.ml

TEST_SRC := \
       tests/test.ml \
       tests/test_ordinals.ml \
       tests/test_storage.ml \
       tests/test_env.ml \
       tests/test_lexi_next.ml \
       tests/test_eval_reduce.ml \
       tests/test_eval_imap.ml \
       tests/test_selection.ml \
       tests/test_array.ml \
       tests/test_shape.ml \
       tests/test_force.ml \
       tests/test_parser.ml \
       tests/test_value.ml


all: main.native test.native


main.native: $(SRC)
	$(OCB) main.native

test.native: $(TEST_SRC) $(SRC)
	$(OCB) -package oUnit -I tests test.native

test.d.byte: $(TEST_SRC) $(SRC)
	$(OCB) -package oUnit -I tests test.d.byte


main.d.byte: $(SRC)
	$(OCB)  main.d.byte

clean:
	$(OCB) -clean

