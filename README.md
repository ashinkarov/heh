# Heh

Heh is a functional programming language with a built-in support for infinite arrays.
The languag is strict, but the infinte structures are lazy.  The language includes three
built-in higher-order constructs: `imap`, `reduce` and `filter` which make it possible
to construct complex array operations that can be often seen in APL or SaC.

One of the main distinctive feartures of the language is that we use ordinals to index
arrays as well as to maintain shapes of the arrays.  This gives a rise to a number of
important static properties that one can observe in Heh.

Heh makes it possible to write generic programs that do not make distinction between
arrays and streams.  One can write truly infinity-polymorphic programs:
```
letrec inc = λa.λv.imap (|a|)|[] { mul |a| 0 <= iv < |a|: (a iv) + v in
inc
```
Keep in mind, that the increment function never specifies whether the shape of `a`
is finite.


The name Heh refers to the Egyptian mythology, where Heh is the god of
infinity.

<img src="https://upload.wikimedia.org/wikipedia/commons/thumb/a/ad/Heh.svg/700px-Heh.svg.png" width=250 alt="Heh -- the god of infinity"/>
