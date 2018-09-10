
## V1 Basics

In this part, the reader will learn about:
* Coq's functional programming language is called Gallina.
* basic data types such as booleans, integers and strings are defined in Gallina and are parts of Coq's standard library.
* simple `Inductive` types
* inductive type with constructors that have arguments
* how to use `Definition` and pattern matching to define functions on inductive types and inductyve type with constructors that have arguments
* the `_` placeholder to avoid introducing too many names
* how to use `Compute` to perform evaluation by simplification
* how to use `Example` for defining unit tests and proving them beginning with `Proof` and terminating with `Qed`.
* how to use `Admitted` to leave things unproven.
* how to use `Check` to investigate the type of things.

The reader will meet:
* the `simpl` tactic for simplification
* the `reflexivity` tactic for equalities
* `Type`
* the `Module` and `End` commands for defining modules

Things that will be alluded to include:
* the possibility of extracting a function to OCaml, Haskell, or Scheme

The `bool`, `true`, `false`, negation `negb`, conjunction `andb`, disjunction `orb` from the Coq library will be redefined.

The book make heavy usages of the `Notation` command, which is can be quite cryptic for beginners.

The natural integers `nat` and their constructors `O` and `S` will be redefined.

A predecessor function which illustrates pattern matching on integers will be introduced.

A more elaborate function which returns a number minus 2 will be introduced.

A recursive function which tests for evenness will be introduced, using the `Fixpoint` command.

Addition, multiplication, subtraction and exponentiation will be redefined with recursive functions.

The reader will learn that arguments of a same type can be grouped together, i.e. the type of the arguments need only be declared once.

`reflexivity` does more than `simpl` because it expands the terms in a such a way that would leave the expression tree difficult to use, while `simpl` leaves things cleaner.

`Theorem`, `Example`, `Lemma`, `Fact`, and `Remark` are internally synonymous.

Here's something interesting.

First, we define a function on answers, but do not specify its body.

{% highlight text %}
Definition foo (a:answer) : answer.
Admitted.
{% endhighlight %}

Then, despite the fact that `foo` function is not specified, we can prove a theorem involving `foo`.

{% highlight text %}
Theorem thm : forall n m:answer, n=m -> foo n = foo m.
intros n m.
intro eq.
rewrite -> eq.
reflexivity.
{% endhighlight %}

This is so because `reflexivity` works whenever the trees on the left and on the right of the equality are the same.

Note on `rewrite`: the arrow points to which side of the equality wins.

To perform case analysis on inductive types, use `destruct`.

To make proof readables, use bullets such as `-`, `+`, `*` and braces `{...}`.


{% comment %}
Open quests:
* Extract a program into an OCaml library and make use of it in an OCaml program.
* Extract a program into a Haskell library and make use of it in a Haskell program.
* Extract a program into a Scheme library and make use of it in a Scheme program.
* Write and understand about CoqIde display options for implicit arguments, coercions, raw matching expressions, notations, all basic low-level contents, existential variable instances, universe levels, and all low-level contents.
* Explain what Coq's `Fixpoint` and recursion has to do with the Y combinator from lambda-calculus.
* Find out what the standard tactics exactly do.
* Find all about this notation thing.
{% endcomment %}
