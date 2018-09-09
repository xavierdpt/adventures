---
layout: post
title:  "Adventures in Coq"
date:   2018-09-07 08:00:00 +0200
categories: something
---

[Coq] is a formal proof and verification system, which allow to proof mathematical statements and certify programs against a specification.

The [documentation section][documentation] has a link to [Software Foundations][sf], a 4-Volumes work about functional programming, theorem proving, operational semantics, Hoare logic, type systems, specification and verification.

The topic of this adventure is to explore this work.

Here's the complete outline of the whole thing.

* Volume 1: Logical Foundations
	* Preface
	* Functional Programming in Coq
	* Proof by Induction
	* Working with Structured Data
	* Polymorphism and Higher-Order Functions
	* More Basic Tactics
	* Logic in Coq
	* Inductively Defined Propositions
	* Total and Partial Maps
	* The Curry-Howard Correspondence
	* Induction Principles
	* Properties of Relations
	* Simple Imperative Programs
	* Lexing and Parsing in Coq
	* An Evaluation Function for Imp
	* Extracting ML from Coq
	* More Automation
	* Postscript
	* Bibliography
* Volume 2: Programming Language Foundations
	* Preface
	* Program Equivalence
	* Hoare Logic, Part I
	* Hoare Logic, Part II
	* Hoare Logic as a Logic
	* Small-step Operational Semantics
	* Type Systems
	* The Simply Typed Lambda-Calculus
	* Properties of STLC
	* More on the Simply Typed Lambda-Calculus
	* Subtyping
	* A Typechecker for STLC
	* Adding Records to STLC
	* Typing Mutable References
	* Subtyping with Records
	* Normalization of STLC
	* A Collection of Handy General-Purpose Tactics
	* Tactic Library for Coq: A Gentle Introduction
	* Theory and Practice of Automation in Coq Proofs
	* Partial Evaluation
	* Postscript
	* Bibliography
* Volume 3: Verified Functional Algorithms
	* Preface
	* Basic Techniques for Permutations and Ordering
	* Insertion Sort
	* Insertion Sort With Multisets
	* Selection Sort, With Specification and Proof of Correctness
	* Binary Search Trees
	* Abstract Data Types
	* Running Coq programs in ML
	* Implementation and Proof of Red-Black Trees
	* Number Representations and Efficient Lookup Tables
	* Priority Queues
	* Binomial Queues
	* Programming with Decision Procedures
	* Graph Coloring
* Volume 4: QuickChick: Property-Based Testing in Coq
	* Preface
	* Introduction
	* A Tutorial on Typeclasses in Coq
	* Core QuickChick
	* Case Study: a Typed Imperative Language
	* The QuickChick Command-Line Tool
	* QuickChick Reference Manual
	* PostScript
	* Bibliography

## V1 Preface

*Each of the texts is literally a Coq script* This follows the trend of other formal softwares such as Mathematica, Maxima or Sage

**Quest idea**: Create a nice Coq document about something.

Building reliable software is really hard. Formal mathematical techniques can help in specifying and reasoning about the properties of software and producing software which has the guarantees of having some stated properties.

Logic is at the core of mathematics and computer science. There are actually a large number of different logics, and the paragraph does not mention which particular logic is being talked about.

Automated theorem provers can state whether some mathematical statements are true or false automatically. Such tools include SAT solvers, SMT solvers and model checkers.

**Quest idea**: Experiment with a SAT solver.

**Quest idea**: Experiment with an SMT solver.

**Quest idea**: Experiment with a model checker.

Proof assistants are interactive, and include Isabelle, Twelf, ACL2, PVS, and Coq, of course.

**Quest idea**: Experiment with Isabelle

**Quest idea**: Experiment with Twelf

**Quest idea**: Experiment with ACL2

**Quest idea**: Experiment with PVS

Coq is an interactive development environment for machine-checked formal reasoning which includes
* a proof-checker
* a large library of common definitions and lemmas
* tactics for constructing complex proofs semi-automatically
* a special-purpose programming language for defining new tactics

**Quest idea**: Define a custom tactic in Coq and use it.

Coq has been used to
* To check the security of the JavaCard platform
* Formal specifications of the x86 and LLVM instruction sets
* Formal specifications of the C programming languages and others.

**Quest idea**: Investigate JavaCard.

**Quest idea**: Investigate LLVM.

**Quest idea**: Investigate the formal specification of some programming language.

Coq has been used to build:
* CompCert, a fully-verified optimizing compiler for C
* CertiKos, a fully verified hypervisor
* Proving the correctness of subtle algorithms involving floating point numbers
* CertiCrypt, an environment for reasoning about the security of cryptographic algorithms
* verified implementations of the open-source RISC-V processor

**Quest idea**: Investigate CompCert

**Quest idea**: Investigate CertiKos

**Quest idea**: Investigate CertiCrypt

The Ynot system embeds "relational Hoare reasoning" in Coq.

**Quest idea**: Investigate Ynot

Coq has been used to develop the first formally verified proof of the 4-color theorem.

Coq has been used to formalize a proof the Feit-Thompson Theorem, which is the first major step in the classification of finite simple groups.

**Quest idea**: Investigate the Feit-Thompson Theorem

Functional programming languages include Haskell, OCaml, Standard ML, F#, Scala, Scheme, Racket, Common Lisp, Clojure, Erlang, and Coq.

**Quest idea**: Do something in Haskell

**Quest idea**: Do something in Ocaml

**Quest idea**: Do something in Standard ML

**Quest idea**: Do something in F#

**Quest idea**: Do something in Scala

**Quest idea**: Do something in Racket

**Quest idea**: Do something in Common Lisp

**Quest idea**: Do something in Clojure

**Quest idea**: Do something in Erlang

**Quest idea**: Write about $$\lambda$$-calculus

Functional programming is about pure functions which have no side effects, which is easier to reason about and parallelize.

**Quest idea**: Write about the Map-Reduce idiom in Hadoop

Functional programming lends itself very well as a bridge between logig and computer science.

Coq is actually a functional programming language.

Two Coq IDEs are Proof General for emacs and CoqIDE.

**Quest idea**: Experiment with emacs, before experimenting with Proog General

Too bad, solutions to exercises are not supposed to be shared.

## V1 Basics

Because they do not have side effect, functional procedures are regarded as concrete methods of computing mathematical functions.

In functional programming, functions are treated as "first-class" values, which can be returned by functions and passed around.

Functional languages include algebraic data types and feature pattern matching and polymorphic type systems.

Coq's functional programming language is called Gallina.

Basic data types such as booleans, integers and strings are defined in Gallina and are parts of Coq's standard library.

Here's an enumeration defined as an inductive type.

{% highlight text %}
Inductive answer : Type :=
| yes : answer
| no : answer 
| unknown : answer.
{% endhighlight %}

Here's a function which toggles the answer.
{% highlight text %}
Definition toggle_answer (a:answer) : answer := match a with
| yes => no
| no => yes
| unknown => unknown
end.
{% endhighlight %}

Here's how to call the function:
{% highlight text %}
Compute (toggle_answer yes).
Compute (toggle_answer (toggle_answer yes)).
{% endhighlight %}

Note: In CoqIDE, "query" commands should not be run from the CoqIDE buffer, because it is supposed to be a file and therefore not interactive. You'll get the following warning:
{% highlight text %}
Query commands should not be inserted in scripts
{% endhighlight %}
Intstead, hit F1, then replace "Search" with a blank and use the input to run the query commands.

Here's how to record a kind of unit test.
{% highlight text %}
Example test_yes_no: (toggle_answer yes) = no.
Proof.
simpl.
reflexivity.
Qed.
{% endhighlight %}

If you trust the OCaml, Haskell or Scheme compilers and Coq's extraction facility, the function toggle_answer can be extracted into a program in one of these languages.

**Quest idea**: Extract a program into an OCaml library and make use of it in an OCaml program.

**Quest idea**: Extract a program into a Haskell library and make use of it in a Haskell program.

**Quest idea**: Extract a program into a Scheme library and make use of it in a Scheme program.

Coq's library define the `bool` type with values `true` and `false`, and  the functions `negb`, `andb`, `orb` for negation, conjonction and disjunction. Notations `||` and `&&` are also defined.

Example:
{% highlight text %}
Compute (andb true false).
{% endhighlight %}

The `Admitted` command is used to skip proofs, and can also be used to define functions without specifying their body.

When using `Compute` with functions which are not defined, they are left unevaluated.

Use `Check` to check the type of an expression.

{% highlight text %}
Check toggle_answer.
Check (toggle_answer yes).
{% endhighlight %}

Inductive types can be parametrized, which each item parametrized differently.

Here's an ugly way of fusing booleans and answers in one type, which features pattern matching  with anonymous variables.

Inductive types are defined by constructor expressions, which have a type of a function into the inductive type being defined, and no body.

{% highlight text %}
Inductive answer_bool : Type :=
  | ab_answer : answer -> answer_bool
  | ab_bool : bool -> answer_bool.

Definition answer_bool_positive (x : answer_bool) : bool :=
  match x with
  | ab_answer yes => true
  | ab_answer _ => false
  | ab_bool true => true
  | ab_bool _ => false
  end.

Example answer_bool_positive_true_true:
  (answer_bool_positive (ab_bool true)) = true.
Proof.  simpl.  reflexivity.  Qed.
{% endhighlight %}

The commands `Module X` and `End` define a module. A variable `x` define in the module can be reffered to outside of the module as `X.x`.

Natural integers `nat` are defined inductively as the `O` constant denonting zero, and the successor `S` denoting addition of 1.

Coq automatically replaces `S` and `0` by the corresponding numbers, both for display and in the input.

Therefore, the following displays as `4`:
{% highlight text %}
Compute (S (S 2))
{% endhighlight %}

Here's something that acts as the predecessor function:
{% highlight text %}
Definition previous (n : nat) : nat :=
match n  with
| O => O
| S p => p
end.
{% endhighlight %}

**Quest idea**: Write and understand about CoqIde display options for implicit arguments, coercions, raw matching expressions, notations, all basic low-level contents, existential variable instances, universe levels, and all low-level contents.

Recursive functions can be defined with `Fixpoint`Fixpoint evenb (n:nat) : bool :=
{% highlight text %}
match n with
| 0 => true
| S 0 => false
| S (S p) => evenb p
end.
{% endhighlight %}

**Quest idea**: Explain what Coq's `Fixpoint` and recursion has to do with the Y combinator from $$\lambda$$ calculus.

**Quest idea**: Find out what tactics such as `simpl` and `reflexivity` exactly do.

When several arguments have same type, they can be grouped together. `Definition f (n : nat) (m : nat)` is equivalent to `Definition f (n m : nat)`

To pattern match on multiple argument, separate the patterns with commas. Example:
{% highlight text %}
Fixpoint minus (n m : nat) : nat :=
match n, m with
| O , _ => O
| S _ , O => n
| S n', S m' => minus n' m'
end.
{% endhighlight %}

Here's how to introduce the notation for `+`:
{% highlight text %}
Notation "x+y" := (plus x y) (at level 50, left associativity) : nat_scope.
{% endhighlight %}

**Quest idea**: Find all about this notation thing.

Equality testing of natural integers is defined by nested pattern matching on both arguments.

`reflexivity` performs some forms of simplication automatically.

`reflexivity` does more than `simpl` because it expands the terms in a such a way that would leave the expression tree difficult to use, while `simpl` leaves things cleaner.

In Coq, `Theorem`, `Example`, `Lemma`, `Fact`, and `Remark` are synonymous.

**Quest idea**: Find whether `intros`, `simpl` and `reflexivity` are primitive or defined with Coq's tactic definition language.

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

**Quest idea**: Find out more about how `rewrite` works, i.e. why in the following, it ends with `(0 + n) * m = 0 + n * m` and not something else, since there are multiple possibilities.

{% highlight text %}
Theorem plus_O_n : forall n : nat, 0 + n = n.
Proof.
  intros n. simpl. reflexivity. Qed.

Theorem mult_0_plus : forall n m : nat,
  (0 + n) * m = n * m.
Proof.
  intros n m.
  rewrite <- plus_O_n.
  reflexivity. Qed.
{% endhighlight %}

To perform case analysis, use `destruct`.

Do make proof readables, use bullets such as `-`, `+`, `*` and braces `{...}`.

## V1 Proof by Induction

To make the following work:
{% highlight text %}
From X Require Export Y.
{% endhighlight %}

Execute the following command first:
{% highlight text %}
coqc Y.v
{% endhighlight %}

*Proof by induction*

When simplification + reflexivity does not work, try case analysis.

When case analysis does not work, try proof by induction.

The `induction` tactic generates a case with the induction hypothesis, which can usually be used later with the `rewrite` tactic.

*Proofs within proofs*

`assert` can be use to prove things using the variables of the main proof. `assert` is useful because it is closure-aware.

*Formal vs. informal proof*

Coq proofs do not show the intermediate proof states, which make them difficult to follow.

## V1 Working with Structured Data

*Pairs of numbers*

Coq defines types, function and notations for definining pairs and extracting the first and second element of the pair.

*List of numbers*

A list is either the empty list `nil` or a an element and another list (`cons`).

Coq define types, functions and notations for working with lists. `[]` is the empty list, `x::l` adds an element to a list, and `[x;...;z]` define a list inline.

Common things to do with lists is to repeat them, get their length, append to a list, get the head or get the tail.

*Reasoning about lists*

Prove that reversing a list does not change its length.

**Quest idea**: Convert a Coq proof to a hiearchical informal proof, so that the levels of details can be expanded at will depending on the familiarity level or something.

`Search` can be used to search theorems according to shape.

With ProofGeneral, use C-c C-a C-a to seach, then C-c C-; to copy/paste the result.

*Options*

Options define a `None` constructor with no value and a `Some` constructor with a value.

In Coq, any inductive type with two constructors support the `if ... then ... else ...` construct.

*Partial Maps*

Define an inductive type for identifiers, and an equality test for identifiers.

Then a partial map is either the empty map, or an identifier with a value and another (smaller ?) partial map.

The `update` function overrides one value.

The `find` function scan the map for a supplied identifier.

**Quest idea**: How can the find function be made smarter, i.e. with better than linear complexity?

## V1 Polymorphisms and Higher-Order Functions

*Polymorphism*

Compare

{% highlight text %}
Inductive list : Type :=
  | nil : list
  | cons : nat → list → list.
{% endhighlight %}

with

{% highlight text %}
Inductive list (X:Type) : Type :=
  | nil : list X
  | cons : X → list X → list X.
{% endhighlight %}

Coq performs some type inference so that it is rarely necessary to express type arguments.

Another keyword is "unification".

The `Arguments` command specifies which arguments to treat implicitely in curly braces.

{% highlight text %}
Arguments nil {X}.
Arguments cons {X} _ _.
Arguments repeat {X} x count.
{% endhighlight %}

Arguments can also be declared as impicity by specifying the implicity with curly braces in the definition itself. Then the arguments are implicity in the body of the definition too.

{% highlight text %}
Inductive list {X:Type} : Type :=
  | nil : list
  | cons : X → list → list.
{% endhighlight %}

Prefixing a term with `@` expose all the arguments defined implicity, for situation where type inference fails.

*Functions as data*

The syntax `fun ... => ...` defines a function inline.

Functionals include `filter`, `map`, `fold`...

Functions can return other functions.

## V1 More Basic Tactics

`apply` works when the conclusion of something match the goal exactly, and leaves the hypotheses of the something as new goals.

`apply Thm with (x:=y)` is useful when the theorem needs something it cannot guess.

`apply Thm with y` works when Coq can figure out where to put the supplied value on its own.

`symetry` is useful to rewrite an equality from right to left.

The constructors of inductive types are injective, and if a value is an instance of some constructor, then it's an instance of no other constructors of that type.

The `inversion` tactics exploit these facts.

`inversion` detects things that cannot work and solve the goals immediately for these cases.

If `H` is hypothesis `A` and `Thm` is `A->B`, then `apply Thm in H` produces a hypothesis which matches `B`.

`symmetry in H` applies the `symetry` tactics on hypothesis `H`.

When a variable is introduced, it is understood that some particular value of this variable is being considered. When using `induction`, pay attention to which variables are in the context.

`generalize dependent n` reverts the effect of `intro` for some particular variable.

`unfold f` unfolds the definition of `f`

`destruct` can perform case analysis on the result of any computation.

{% highlight text %}
destruct (plus n 1)
{% endhighlight %}

Adding `eqn` saves the equality of each cases.
{% highlight text %}
destruct (plus n 1) eqn:E
{% endhighlight %}

## V1 Logic in Coq

`Prop` is the type of propositions.

Conjunction `/\` and `split` and `desctruct`.

Applying a projection thereom on a conjunction helps to keep only the part we're intersted in.

Disjunction `\/`, `left` and `right`.

Negation `~` and `exfalso`.

This command
{% highlight text %}
Require Import Coq.Setoids.Setoid.
{% endhighlight %}

allows `rewrite` and `reflexivity` to exploit `iff` statements efficiently.

`exist` performs an implicit destruction with introductions.

The tactic `exist (witness)` provides a witness to an existential.

The proposition which states that some element is in a list is a recursive proposition which can be defined with `Fixpoint` and pattern matching.

Another possibility is to define proposition inductively.






[Coq]: https://coq.inria.fr/
[documentation]: https://coq.inria.fr/documentation
[sf]: https://softwarefoundations.cis.upenn.edu/
