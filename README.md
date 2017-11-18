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

# Results and work in progress

Currently, Heh demonstrates that the concept described in [this paper](https://arxiv.org/abs/1710.03832)
can be implemented.  We have formalized semantics of the language [here](https://github.com/ashinkarov/heh/blob/master/semantics/lambda-omega-semantics.pdf).

We have shown that the number of array equalities from various array algebras hold for infinite arrays as well.
As an example, consider `drop |a| (a ++ b) == b`, where `a` and `b` are of infinite shape, `++` is
concatenation over the first axis and `drop` is an inverse of `++`.

Currently we are working on:
  * Designing a type system for Heh.  The main challenge is to keep the type system decidable,
    yet propagate as much of the shape information as possible.  Knowing shapes of all the arrays
    statically vastly improves the runtime.  Currently we are investigating whether the
    [SaC](http://www.sac-home.org/doku.php) approach of combining sub-typing and intersection types
    is powerful enough.  Going full dependent types is an option, but we will use this if everything
    else would fail.  Also, how excalty one needs to treat ordinals in types is far from obvious.
    
  * Compiling Heh.  If heh programs only use non-recursive finite imaps can be directly transformed
    to SaC programs, which are known to deliver good performance.
    
    Infinite recursive imaps are more challenging.  We didn't fix representation for imaps at
    runtime.  Most likely we want to treat them as hash-tables, where every entry stores a contiguous
    piece of memory, representing an index subspace.
    
    Memory management is fun.  SaC uses reference counting, which is efficient in the strict and finite
    array scenario.  Here, as imaps can be infinite and recursive, most likely we'd have to combine 
    reference counting and garbage collection.
    
  * Proving programs in Heh.  Heh treats infinite structures without using co-induction.  It uses
    transfinite induction instead.  Can we use this to take and advantage over co-inductive data structures
    is not yet clear.
    
  * Streaming primitives.  We have seen that a number of streaming primitives can be implemented in Heh
    right now.  Whether it is sufficient for all the streaming scenarios is not clear.  Also, we didn't
    properly investigate how to treat finite streams.

The above list is not exhaustive, and a number of open question still remain.
In case you are interested in joining to research around Heh, please contact
[Artem Shinkarov](mailto:artyom.shinkaroff@gmail.com).  We are open for collaboration.


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
