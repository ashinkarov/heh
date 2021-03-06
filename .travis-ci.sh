wget https://raw.githubusercontent.com/ocaml/ocaml-travisci-skeleton/master/.travis-ocaml.sh
sh .travis-ocaml.sh

eval `opam config env`

export OPAM_PACKAGES='ocamlfind menhir ounit'

# install packages from opam
opam install -q -y ${OPAM_PACKAGES}

make

# run the unit tests
./test.native

# run all the examples
./.run-examples
