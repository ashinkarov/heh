# Heh

[![Build Status](https://travis-ci.org/ashinkarov/heh.svg?branch=master)](https://travis-ci.org/ashinkarov/heh)

Heh is a functional programming language with a built-in support for infinite arrays.
The language is strict, but the infinite structures are lazy.  The language includes three
built-in higher-order constructs: `imap`, `reduce` and `filter` which make it possible
to construct complex array operations that can be often seen in APL or SaC.

One of the main distinctive features of the language is that we use ordinals to index
arrays as well as to maintain shapes of the arrays.  This gives a rise to a number of
important static properties that one can observe in Heh.

Heh makes it possible to write generic programs that do not make distinction between
arrays and streams.  One can write truly infinity-polymorphic programs:
```
λa.λv.imap |a| { _(iv): (a iv) + v
```
Keep in mind, that the increment function never specifies whether the shape of `a`
is finite.


The name Heh refers to the Egyptian mythology, where Heh is the god of
infinity.

<img src="https://upload.wikimedia.org/wikipedia/commons/thumb/a/ad/Heh.svg/700px-Heh.svg.png" width=250 alt="Heh -- the god of infinity"/>

# Building the interpreter

The following dependencies are required:
  * Ocaml version >= 4.3;
  * ocamlbuild
  * oUnit _if you wan to run unittests_

To build the interpreter run `make` within the top-level directory which by default
creates `main.native` (the interpreter) and `test.native` (unit tests).

Building the interpreter without unit tests can be acheived by `make main.native`.

# Running the interpreter

An interpreter reads a file and executes the program.  Consider an example:

```bash
$ echo "2 + 2" | ./main.native /dev/stdin
2 + 2
res: p3 = 4
$ echo "(imap [omega] {[0] <= iv < [omega]: iv.[0]).[42]" > /tmp/x.heh
$ ./main.native /tmp/x.heh
((imap [ω]|[] { [0] <= iv < [ω]: (((iv).([0])))).([42]))
res: p14 = 42
```
The output contains:
  1. the text of a program
  2. the resulting pointer and value of the evaluated program.
  
The interpreter comes with a few flags, which description is available via `./main/native --help`.

The interpreter comes with a number of examples available in the `examples` directory.

# Testing

The unit tests can be run as follows `./test.native`.

This repository uses travis continuous integration.  See `.travis.yml` file for more details.

# Syntax hilighting

Heh comes with a syntax highlighting description for Vim.
Copy `vim/heh.vim` into `~/.vim/syntax` to make use of it.
