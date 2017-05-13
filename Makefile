OCB := ocamlbuild -j 8 -use-ocamlfind -use-menhir

SRC := ast.ml \
       main.ml \
       lexer.mll \
       parser.mly \
       ordinals.ml \
       storage.ml \
       env.ml \
       eval.ml

all: main.native


main.native: $(SRC)
	$(OCB) main.native

main.d.byte: $(SRC)
	$(OCB)  main.d.byte

clean:
	$(OCB) -clean

