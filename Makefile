OCB := ocamlbuild -j 8 -use-ocamlfind -use-menhir

SRC := ast.ml \
       main.ml \
       lexer.mll \
       parser.mly \
       ordinals.ml \
       storage.ml \
       env.ml \
       eval.ml \
       globals.ml

TEST_SRC := \
       tests/test.ml \
       tests/test_ordinals.ml \
       tests/test_storage.ml \
       tests/test_env.ml

all: main.native test.native


main.native: $(SRC)
	$(OCB) main.native

test.native: $(TEST_SRC) $(SRC)
	$(OCB) -package oUnit -I tests test.native

main.d.byte: $(SRC)
	$(OCB)  main.d.byte

clean:
	$(OCB) -clean

