OCB := ocamlbuild -j 8 -use-ocamlfind -use-menhir

SRC := ast.ml \
       main.ml \
       lexer.mll \
       parser.mly

all: main.native


main.native: $(SRC)
	$(OCB) main.native

clean:
	$(OCB) -clean

