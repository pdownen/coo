Coo
===

A friendly little programming language to talk about co-things.


Examples
========

Examples of Coo programs demonstrating different language features and
programming patterns are given in the `examples` directory.  These include:

* `list.coo`: Some list-processing functions standard in functional programming,
  along with a more parsimonious (i.e., resource wise) version of the `filter`
  function.

* `stream.coo`: Well-known examples of functions on infinite streams defined
  using copattern matching.

* `iterating.coo`: Various takes on higher-order iterators and their
  compositional extensions with a stateless (or state-parameterized)
  object-oriented style.

* `handling.coo`: Multiple ways of handling failure, including alternative
  commands attach to pattern-matching binds, multiple continuations (pointing
  out the error path and main return path), and preemptively capturing and
  calling the failure alternative during a reaction.

* `classical.coo`: Encodings of classical logic axioms as Coo operations.

* `pigeon.coo`: A version of the prescient filter function on infinite streams,
  and an implementation of the infinite pigeonhole principle as an effectful
  stream function.

* `simple-types.coo`: A selection of examples (many from the above files) with
  type annotations added to run with type checking on.


Installation
============

Coo is implemented in Haskell. To build it, you'll need

* GHC   - 9.14.1
* Cabal - 3.16.1

If you don't have these installed already (or have older versions installed),
consider using ghcup [https://www.haskell.org/ghcup/] to get these ready.

Once your system is running the above versions of GHC and Cabal, you can build
the Coo interpreter by running the following command in this root directory:

> cabal build

From there, you can simply run the built executable directly, or through `cabal`
using

> cabal run

The `coo` executable takes optional command-line arguments, such as the name of
a file to run directly (see the `--help` for more information on command line
arguments).  If no arguments are passed, you will automatically enter the
interactive REPL, where you can input statements directly or load files with the
REPL instruction `#run "path/to/file.coo"`.  To pass command-line arguments when
starting `coo` through `cabal`, you can prefix those arguments with an initial
`--`, such as:

> cabal run coo -- examples/pigeon.coo

or, for strictly enforcing static types,

> cabal run coo -- examples/simple-types.coo --type=error
