Coo
===

A friendly little programming language to talk about co-things.


Introduction
============

Coo is an experimental research programming language based heavily on ideas
coming from the classical sequent calculi---such as Gentzen's LK---and their
connection with computation, abstract machines, and compilers.  More
specifically, Coo is a playground to interactively experiment with:

* Duality in programming languages and types.

* Pattern and copattern matching as central program design concepts.

* Exotic forms of structured, non-functional control flow and error handling.

* Infinite objects and codata types.

* The connection and interplay between functional and object-oriented paradigms.

* Practical Curry-Howard correspondence between classical logic and programs.


Quick Tour
==========

Like functional languages, Coo avoids mutable state, preferring instead
persistent immutable variables and data structures.  Yet, like imperative
languages, Coo maintains a strict syntactic distinction between *expressions*
which (are expected to) return an answer versus *statements* or *commands* which
merely execute.

For example, the classic introductory program is a single statement:

```
print "Hello, world!";
```

Notice that `print` is an ordinary function (not a special command), and
parentheses are optional with function calls, making `print("Hello, world!")`
an equivalent expression.

Functional Programming
----------------------

Coo's syntax is loosely based on Standard ML's, where functions are defined by a
keyword `fun` and values are defined by a keyword `val`.  For example, `answer`
will be 120 in the following:

```
fun | fact(0) = 1
    | fact(n) = n * fact(n-1);
    
val answer = fact 5;
```

Also like Standard ML, functions are curried by default.  The standard `map`
over a list can be defined as:

```
fun | map {f} Nil        = Nil
    | map {f} Cons[x,xs] = Cons[f x, xs];
```

Notice that the first argument to `map` is wrapped in curly braces as `{f}`
(a.k.a.  "suspenders").  This is how suspended code---such as functions---can be
passed as arguments or stored in data structures.  Suspenders can be opened
during pattern matching, like in the definition of `map`, which matches the same
syntax of the call sites.  For example, the partial application of `map` to the
`fact` function is `map {fact}`, which is still waiting for a list argument to
apply `fact` to each of its elements.


Infinite Codata
---------------

However, unlike Standard ML, we can program with infinite objects using codata
and copattern matching, too!  For example, here is a stream `nats` of all the
natural numbers 0, 1, 2, 3:

```
fun | count(n).Head = n
    | count(n).Tail = count(n+1);

fun nats = count 0;
```

`nats` is a special case of `count`, which takes an argument and then becomes a
stream responding to two possible destructors: `Head` asks for the first element
of the stream and `Tail` asks for the rest of the stream after the first element
is dropped.

Just like with lists, we can map a function over every element of a stream like
so:

```
fun | maps {f} {xs}.Head = f(xs.Head)
    | maps {f} {xs}.Tail = maps {f} {xs.Tail};
```


Structured Go To
----------------

Perhaps the most unique aspect of Coo is its approach to *structured goto
statements*.  These are structures in two ways:

* The "labels" (represented by continuations) are statically scoped just like
  any other variable, and live in the same namespace as value identifiers.
  
* The continuations can actually be data structures themselves.  The evaluation
  context can be pattern-matched against, and one can jump *to* a structure, not
  just a label.
  
For example, continuation labels names can be introduced by the `do` keyword,
which "catch" the output of some statements (the result of a `go ... to ...`)
and returns it as the `do` expression's value.  For example, here is a
definition of the classical *law of the excluded middle* as a function of no
arguments:

```
fun excluded_middle = do here => {
    fun go lie x to there = go Yes[x] to here;

    go No[{lie}] to here;
};
```

Notice that the local function `lie` defined internally inside of
`excluded_middle` is an equation between `go to` statement, rather than an
equation between expressions as usual in functional languages.  When `lie` is
called with an argument `x` and in a context named `there`, it discards that
context and go to `here` again with the answer `Yes[x]`.  This internal function
is packaged up and put inside the other option, `No`, which is the first answer
that `excluded_middle` returns.  Opening this box and calling `lie` will rewind
again to the place where `excluded_middle` originally ran, providing the
opposite answer instead.

It can be burdensome if we *always* have to come up with a name whenever we want
to `do` something.  That's why you can leave the label implicit, which picks an
arbitrary (invisible) name for you automatically.  This is accessible within the
`do`'s scope by simply performing a `go` without an explicit `to` target.  For
example, the purely functional collatz function

```
fun collatz n if
  | even n = n / 2
  |        = n * 3 + 1;
```

could be rewritten in a more imperative style like so:

```
fun collatz(n) = do => {
  if even n => go n / 2;
  go n * 3 + 1;
};
```

Even though the static link between the unnamed `do` and `go` is given by their
textual positions, it still persits inside closures just like any other named
variable.  For example, the shortest definition of `callcc` in Coo is

```
fun callcc {h} = do =>
    go h {fn x to _ => go x};
```

The unnamed `go x` is used inside of a first-class function passed to `h`, but
will still be statically linked to *this* textual `do` no matter how `h` uses
it.


Exotic Error Handling
---------------------

This gives us several ways of threading control flow around exceptional
circumstances.  For example, a standard way to model a "safe division" operator,
that guards against divide-by-zero errors, could be done by a sum type and
returning a `Nothing` in the case that the operation is impossible.

```
fun | safe_div x 0 = Nothing
    | safe_div x y = Just[x/y];

fun undo_divide x y = do => {
    val Just[a] = safe_div x y
        else Nothing => go Nothing;
    pprint a;
    val Just[b] = safe_div x a
        else Nothing => go Nothing;
    pprint b;
    go Just[b];
};
```

The `undo_divide` operation does two integer divisions in a row, so that they
undo each other and the answer is always `y` if no error occurs.  Notice that,
rather than a rightward cascade of pattern-matching statements, the
`undo_divide` operation, we have the option to provide an alternative
error-recovery `else` class saying what happens if the pattern-match fails
(similar to Idris-style pattern-matching binds).  If either `safe_div` returns
`Nothing`, then the function immediately stops with `Nothing` as the result.

However, there is another way to model safe division, with multiple
continuations!  `par_div` has two possible return paths; one to use if the
division is successful, and one if the error is encountered and avoided.

```
fun go par_div x y to {err}, {main} if
  | y == 0 = go to err
  |        = go x/y to main;

fun undo_divide x y = do => {
    fun err = do () => go Nothing;
    val a = par_div x y {err};
    pprint a;
    val b = par_div x a {err};
    pprint b;
    go Just[b];
};
```

This time, `undo_divide` is still a pure function returns a sum type, but
internally it creates a single exception handler `err` that gets passed to both
`par_div` calls.  If either one invokes that handler, it jumps to the end of its
caller `undo_divide` immediately with a `Nothing` result.


Examples
========

More examples of Coo programs demonstrating different language features and
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
* Cabal - 3.18.1

If you don't have these installed already (or have older versions installed),
consider using ghcup [https://www.haskell.org/ghcup/] to get these ready.

Once your system is running the above versions of GHC and Cabal, you can build
the Coo interpreter by running the following command in this root directory:

> cabal build

From there, you can simply run the built executable directly, or through `cabal`
using

> cabal run

There is also a provided short `setup.hs` script that performs these two
commands in sequence, building the language implementation and then running it
on a short Coo program to ensure that it is working and available.  `setup.hs`
assumes that you already have GHC and Cabal installed on your system.


A Note About Unicode
--------------------

Some unicode characters are used in printing out certain meta-data when
displaying the various intermediate representations used by the translation.
Sometimes, Windows terminals don't display unicode characters correctly by
default.  This is not an issue for normal evaluation, and should still pass the
tests checking intermediate representations, but it is not easy to look at.

If you are on a Windows machine, and happen to see what looks like misprinted
unicode characters when running with the `--dumpdc` option, first try making
sure that your terminal of choice is properly supporting utf8 encoding.  One way
to do this globally on Windows is through the "Language & Region" settings page
(on modern Windows machine, you can search for "Language settings" in the start
menu).  Expanding "Windows display language" reveals an option "Use Unicode
UTF-8 for worldwide language support", which enables the expanded character set
in built-in Windows terminals (like powershell or cmd.exe).


Running
=======

The `coo` executable takes optional command-line arguments, such as the name of
a file to run directly (see the `--help` for more information on command line
arguments).  If no arguments are passed, you will automatically enter the
interactive REPL, where you can input statements directly or load files with the
REPL aside instruction `#run "path/to/file.coo"`.  To pass command-line
arguments when starting `coo` through `cabal`, you can prefix those arguments
with an initial `--`, such as:

> cabal run coo -- examples/pigeon.coo

or, for strictly enforcing static types,

> cabal run coo -- examples/simple-types.coo --type=error

An in-between option is type *warnings*, which perform type checking and display
type errors, but do not prevent execution, letting statically ill-typed programs
continue on by checking actual types dynamically at runtime.  This is available
through either the `--type=warn` command-line option, or in REPL through the
aside instruction `#type warn`.

A list of the available interactive REPL aside instructions is given by `#help`.


Testing
=======

To aid with verification and testing, a collection of 36 isolated test cases is
provided with an automated test suite, which covers all the given examples in
the accompanying paper and its appendix.  This is not an exhaustive,
machine-checked proof of the main theorem statements.  Rather, it provides
multiple examples that the provided implementation implements (a superset of)
the same translation, operational semantics, type system as described.

You can run all tests with the usual default Cabal command

> cabal test

which will evaluate each of the 36 example Coo programs through the command-line
interface in multiple ways, and then compare the output with expected results.
Each example is configured automatically so that all 363 individual tests should
PASS at the end of `cabal test` to be considered correct.


Anatomy of a Test Case
----------------------

Each isolated test case can be found in an individual `.coo` program file in the
`test/case/` directory.  The expected results of running a test case
`test/case/<name>.coo` are described in up to four similarly-named files:

* `<name>.out` gives the expected output, that running `<name>.coo` will print
  to standard out during execution.
  
* `<name>.err` gives the expected *runtime* error messages that are printed to
  standard error while `<name>.coo` executes.
  
* `<name>.terr` gives the expected *compile time* static type checking messages
  that are printed to standard error *before* `<name>.coo` executes.
  
* `<name>.ir` gives a dump of various states of intermediate representations of
  the source code, including, in order:
  
  1. a reprint of the parsed code as-is,
  2. the polarity-correction version of that same code,
  3. a simplification of the source code,
  4. the immediate translation of the source code into *unfocused* Dual Core,
     making using of the syntactic sugar where the arguments to constructors
     (like pairs `(M,N)` or tagged `Tag[M]`) may not be values syntactically.
  5. the *focused* form of that same Dual Core code, such that all arguments to
     constructors are immediate syntactic values.
     
  To visually distinguish between the focused and unfocused forms, the unfocused
  forms forms are printed in between single angle brackets `‹...›`, whereas the
  focused forms (where all arguments must already be syntactic values) are
  printed in between double angle brackets `«...»`.
  
If any of these files is missing, then that implies that the associated output
should be blank.  Except for the internal representation `<name>.ir` file, which
are only provided for small enough example programs for legibility of the
step-by-step comparison.

The automated test suite then evaluates each test case `test/case/<name>.coo` in
three different modes, and the actual result of each mode is compared against
the above expectations:

1. First, `<name>.coo` is run with *no static type checking*.  In this mode,
   automatic polarity correction takes place as usual, but after that the
   program is immediately translated, focused, and executed.  The expectation is
   that the standard out matches `<name>.out` exactly and standard error matches
   `<name>.err`, and `<name>.terr` is irrelevant.
   
   You can manually run a test case in this mode and inspect the result with
   
   > cabal run -- test/case/<name>.coo
   
2. Second, `<name>.coo` is run with *strict static type checking*.  In this
   mode, the type checker analyzes the program before it runs, and any type
   error prevents execution.  The expectation is that if `<name>.terr` is
   non-empty, then the type error message printed to standard error matches the
   *initial part* of the file, up to (and not including) the first horizontal
   line `----...----`; if so, then *nothing else* is printed to either standard
   error or output.  Otherwise, if `<name>.terr` is missing/empty, then the
   behavior is exactly as the previous mode with no static type checking.
   
   You can run a test case with static type errors and inspect the result with
   
   > cabal run -- test/case/<name>.coo -terror
   
3. Third, `<name>.coo` is run with *static type warnings*.  This mode combines
   the behavior of the above two: the type checker analyzes the program before
   it runs to look for errors, but the program will always run whether or not
   errors are present.  Because this mode translates and runs the program no
   matter what, there is a *second* round of type checking on the internal Dual
   Core representation as well.  Thus, any type errors in `<name>.terr` will be
   repeated twice: first for the source code type checker, and second on the
   dual core code that comes from its translation.
   
   The expected result of this mode is that if `<name>.terr` is non-empty, then
   its *full* contents will always be present as the *first* part printed to
   standard error.  After that will be exactly the same content as `<name>.err`
   on standard error, as well as the contents of `<name>.out` printed to
   standard out.
   
   You can manually run a test case with static type warnings yourself with
   
   > cabal run -- test/case/<name>.coo -twarn
   
4. Optionally, if a test case has expected internal representations given in
   `<name>.ir`, then the code will be passed to the system an additional time to
   generate the code from a Dual Core dump.  The output from the Dual Core dump
   should match the contents of `<name>.ir`.
   
   You can generate the internal representations for any test case yourself with
   
   > cabal run -- test/case/<name>.coo --dumpdc


Categories of Tests
-------------------

For coverage, the test cases intentionally include Coo programs that have static
type checking and/or dynamic runtime errors in them.  Since both of these kinds
of errors are independent in practical programs, there are four different
categories of tests.

1. Type Error + Runtime Error: this identifies an runtime error that is caught
   in advance by the type system.  Test cases in this category are:
   
   * crash
   * mispolar
   
2. Type Error + Runtime Success: this identifies a case where the type system
   rejects a program, but there is not actually any error at runtime.  This
   could be either due to the simple type system being too conservative, or
   because not enough type annotations are provided for the bidirectional type
   checker to analyze and synthesize types.  These cases can be successfully run
   in dynamic typing or type warning modes.  Test cases in this category are:
   
   * abc
   * pairs-poly
   * pairs-wrong
   * sizing
   * collecting
   * yielding
   * fast-product
   * type-polarity-mismatch
   
3. Type Success + Runtime Error: this identifies the gaps in the type system,
   where it doesn't catch all possible runtime errors.  A typical example of
   this kind of case is division by zero.  Test cases in this category are:
   
   * and-eager

4. Type Success + Runtime Success: this identifies programs which pass the
   static type checker, and successfully produce their output with no errors at
   runtime.
   
   All other test cases are in this category.


List of Test Cases
------------------

Here is a list of all 36 test cases, their high-level description, and any
correspondence to the accompanying paper (if they are mentioned in the paper).

**Note:** The implementation of the type system goes beyond the simple type
system formalized in the paper.  Notably, it includes an implementation of
(equi)recursive types.  Moreover, algorithmic type checking is organized as a
bidirectional type system, so annotations are required on function headers, or
in places where a type must be inferred from an un-inferrable form (such as an
introduction form like `Cons[1, Nil]`).


* hello: a simple "Hello, world!" style program.

* abc: (pretty) prints a list containing the strings "a", "b", and "c".  This
  fails the static type checker, because it assumes that `pprint`'s argument is
  an `int`.

* crash: tries to concatenate a string and a number, which raises an error at
  both type-checking time and runtime.

* pairs-poly, pairs-mono, and pairs-wrong: three different variants of the first
  example of pair functions: first and second projection, and duplicating an
  argument into a pair of the same value twice.  `pairs-poly` uses these
  functions "polymorphically" at different types, even though this doesn't match
  their type signature (causes a type error, but no runtime error).
  `pairs-mono` fixes the type error by duplicating the same function definitions
  at different types. `pairs-wrong` adds an error to the definition of the `snd`
  function to return the first value instead, which is detected and rejected by
  the static type checker.
  
  * This tests the `fst`, `snd`, and `dup` functions from Section 2.1.

* abs: An absolute value function, written in terms of conditional pattern
  guards.
  
  * This tests the `abs` function from Section 2.1.

* match-loop: an inline iterative loop, written in terms of a recursive `match`
  statement instead of a recursive function, that prints even numbers from 0 to
  100.
  
  * This tests the unnamed loop in Appendix A.1.

* fact: the legally-mandated factorial function.

* collatz: an imperative-style version of the collatz function.

  * This tests the `collatz` example from Section 2.4.

* sum: adds up the numbers in a list.

  * This tests the `sum` example from Section 2.1.

* map: the standard functional programming higher-order function for mapping an
  operation over the elements of a list.
  
  * This tests the `map` example from Section 2.2, including the inline
    definition of a recursive function (`fact`) as an anonymous lambda.

* and-eager, and-lazy: implements boolean `and` as a standard (eager) function,
  as well as a short-circuiting (lazy) version.  The short-circuiting `and_lazy`
  can skip evaluating the second argument if the first one is `False`, avoiding
  runtime errors.
  
  * This tests the `and_eager` and `and_lazy` functions from Section 2.2.

* always, count, powers, zigzag: a series of functions that build infinite
  streams in different ways.
  
  * This tests the stream functions of the same name from Section 2.3.

* range, sizing, collecting, iterating, yielding: a series of extensions on an
  object-oriented use of copatterns to model `range` objects with different
  methods for iterating numbers in a given range.
  
  * This tests the `range`, `sizing`, and `collecting` functions from Section
    2.3, as well as stateful `yielding` from Appendix A.3.

* fast-product: multiplies the numbers in a list, but immediately short-circuits
  to the end if a 0 is encountered anywhere in the list, aborting any pending
  multiplicaton operations waiting on the stack.
  
  * This tests `product` from Appendix A.1.

* safe-div, par-div: two different styles of safely handling exceptions when
  dividing by potentially zero values.
  
  * This tests `safeDiv`, `undoDivide`, `parDiv`, and `undoDivide'` from
    Appendix A.2.

* fizzbuzz, divide2: two different tests of the `else` clause of a reaction,
  used to name the handler for when pattern-matching fails.  `fizzbuzz` is the
  common programming example, and `divide2` fixes two divisions at the same time
  by replacing 0 denominators with nonzero defaults.
  
  * This tests `fizzbuzz` and `divide2` in Appendix A.2.

* parsimonious-filter: a memory-optimized version of the standard filter
  function that only allocates `Cons` cells when surrounding a modified list
  tail.  In other words, this filter function *shares* (without reallocation)
  the longest common suffix of the input list that is unchanged by filtering.
  
  * This tests `parsimoniousFilter` from Section 2.5.

* prescient-filter-short, prescient-filter-long: a "prescient" version of an
  infinite filter function that can take an endless stream of input and decide
  if the given predicate succeeds or fails an infinite number of times
  (producing an infinite stream of only successes or only failures).  The
  "short" test shows what happens "pre-switch" when only a small amount of the
  filtered stream is observed.  The "long" version is exactly the same, except
  that the filtered stream is observed a few elements deeper, having the effect
  of revising the shorter answers to be consistent with the longer ones.
  
  * This tests `prescientFilter` from Section 2.5.

* pigeons-short, pigeons-long: uses the prescient filter function to implement
  the mathematical principle of the infinite pigeonhole principle: if you have
  an infinite number of pigeons and only finite (specifically, 2) holes, then
  one hole must contain infinite pigeons.  Similar to prescient-filter, this
  includes a short and long version, which shows how the initial shorter answers
  are retroactively updated to be consistent with the deeper observations that
  come later.
  
  * This tests `infinitePigeons` from Appendix A.4.

* classical: encodings of the computational content for various axioms of
  classical logic.
  
  * This tests the functions in Remark 2.1.

* mispolar: shows what happens when there is a polarity mismatch in the program,
  specifically, when the suspender braces `{...}` don't line up.
  
* type-polarity-mismatch: shows what happens when the given type annotation
  doesn't match the inferred/corrected polarity of a program.  The type system
  flags an error, but this example runs successfully nonetheless.


On Validation of the Test Harness Itself
----------------------------------------

Since the test harness is configured so that *every* check should be passed, we
should ask if it is actually checking anything at all (instead of simply saying
"yes" to everything regardless of behavior).  How can we confirm that the
expectations given in `test/cases` really match the program itself?

The testing harness is internally configured with the list of test cases to
consider, along with their planned properties (does it run successfully? does it
type check successfully? should the internal representations be checked?).  If
the given expectations do not match with this internal configuration, then
errors will be flagged during testing.  For example, if the internal
configuration doesn't expect a runtime or compile-time error, then it expects a
successful exit code; otherwise, it expects an error code.  If an output or
error message is assumed blank because it is missing from `test/cases` but one
is produced at runtime, then that will show up as a failed case.

To test the testing harness, there is an intentionally broken test case
(`broken-test.coo`) provided in `test/cases` that the testing harness will
detect and fail.  You can check that `broken-test` is indeed a broken test by
uncommenting the case configuration in `tests/Main.hs` on line 66.


Built-in Operations
===================

A few primitive operations are provided to help work with basic types---numbers
and strings---as well as input and output.

List of Operations
------------------

* Equality operations: these work on any two values of any two types, and
  compare values structurally (rather than something like pointer equality).
  Note that the shapes of the value must be the same (the number of tuple
  components and their associativity, and the tags with their exact names).  Any
  two atomic values (integer, float, or string) in the same position must have
  the same type and value to be considered equal.
  
  The *binary infix* equality operations are:
  
  - `==` for equals
  - `/=` for not equals (opposite of `==`)

* Inequality operations: these work on any two numbers.  If both arguments are
  integers, then integer comparison is used.  Otherwise, floating-point
  comparison is used, and the non-float argument (if any) is promoted to a
  float.
  
  The *binary infix* comparison operations are:
  
  - `<` for less than
  - `>` for greater than
  - `=<` for less than or equal to (opposite of `>`)
  - `>=` for greater than or equal to (opposite of `<`)

* Arithmetic operations: these work on any two numbers.  If both arguments are
  integers, then an integer is returned.  Otherwise, a floating-point is
  returned, and the non-float argument (if any) is promoted to a float.
  
  The *binary infix* arithmetic operations are:
  
  - `+` addition
  - `-` subtraction
  - `*` multiplication
  - `/` division
  - `^` exponentiation
  - `%` modulo remainder
  
* Numeric conversions: these explicitly convert between integers and
  floating-point numbers.
  
  - `float` converts any number to a float (does nothing if already a float)
  - `round` rounds to the nearest integer
  - `floor` rounds to the greatest lower bound integer (i.e., always down, truncation)
  - `ceiling` rounds to the least upper bound integer (i.e., always up)
  
* `concat` concatenates to strings together

* `print` prints a string exactly as given to standard output

* `pprint` (a.k.a. "pretty print") automatically converts any value to a string,
  then prints it to standard output
  
* `run_file` takes a file path string pointing to a Coo program, then runs the
  program for its side effects.  Note: unlike the `#run` REPL aside instruction,
  `run_file` is a normal function and does not introduce any bindings from that
  file into the current scope.

* `exit` ends the program immediately


Type Signatures
---------------

The built-in primitive types are:

* `int`
* `float`
* `string`
* `bool`, which is really just a shorthand for the enumeration `[False | True]`.

Due to the simple type system, some of the above build-in functions have more
restricted static type signatures compared to their dynamic runtime capability.
Some operations (like (in)equalities, arithmetic) which make sense at two
different types (integer, floating-point) are duplicated at different names with
different type signatures.  For numeric operations, the convention is that the
standard name is assigned an integer type, and appending a `~` at the end is the
same operation on floating-point types.

Integer operations:
```
(_ == _) : int, int ~> bool
(_ /= _) : int, int ~> bool
(_ >= _) : int, int ~> bool
(_ =< _) : int, int ~> bool
(_ > _)  : int, int ~> bool
(_ < _)  : int, int ~> bool

(_ + _) : int, int ~> int
(_ - _) : int, int ~> int
(_ * _) : int, int ~> int
(_ / _) : int, int ~> int
(_ ^ _) : int, int ~> int
(_ % _) : int, int ~> int

float : int ~> float
```

Floating-point operations:
```
(_ ==~ _) : float, float ~> bool
(_ /=~ _) : float, float ~> bool
(_ >=~ _) : float, float ~> bool
(_ =<~ _) : float, float ~> bool
(_ >~ _)  : float, float ~> bool
(_ <~ _)  : float, float ~> bool

(_ +~ _) : float, float ~> float
(_ -~ _) : float, float ~> float
(_ *~ _) : float, float ~> float
(_ /~ _) : float, float ~> float
(_ ^~ _) : float, float ~> float
(_ %~ _) : float, float ~> float

round   : float ~> int
floor   : float ~> int
ceiling : float ~> int
```

String operations:
```
concat : string -> string ~> string
```

Input-output operations:
```
print  : string ~> ()
pprint : int ~> ()

run_file : string ~> ()
exit : {}
```
