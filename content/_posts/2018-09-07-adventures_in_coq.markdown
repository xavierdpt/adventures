---
layout: post
title:  "Adventures in Coq"
date:   2018-09-07 08:00:00 +0200
categories: something
---

[Coq] is a formal proof and verification system, which allow to proof mathematical statements and certify programs against a specification.

The [documentation section][documentation] has a link to [Software Foundations][sf], a 4-Volumes work about functional programming, theorem proving, operational semantics, Hoare logic, type systems, specification and verification.

The topic of this adventure is to explore this work.

Reproducing selected parts of the work offers little value. We also do not give any solution to the exercises. Instead, we try to address the needs of the following kind of readers.

* Readers who started reading and left in the middle a quite long time ago. These readers want to have their memory refreshed.
* Readers who already know about Coq. These readers want to know what they will find without spending hours sifting through the tedious parts.

Other goals are the following:
* Summarize all the coq features introduced in the course, and say whether they are explained in detail or merely alluded too.
* Summarize the core ideas.
* Introduce some personal derived work inspired from the course.

## Complete outline

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

{% include SFV1Preface.markdown %}

{% include SFV1Basics.markdown %}

{% include SFV1Induction.markdown %}

{% include SFV1Lists.markdown %}

-----

Stopped here.

-----

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

## V1 The Curry Howard Correspondance

A proof is a program that proves a given type exists.

A program is a proof that something of the type of the program exists.

When doing proofs, the focus is on the type, and the exact evidence supplied to prove the type does not really matter.

When writing programs, the focus is on the evidence, and the type of it does not really matter.

For instance, when proving that a function from nat to nat exists `nat -> nat`, any function will do, but we are usually interested in particular functions from nat to nat, and on their properties.

**Quest Idea**: What would it mean to think about the properties of a proof of something ? Is to possible to make two different proofs, and prove that one of the proof has a property that the other has not ?

Proofs are programs that manipulate evidence. 

It's possible to write proof objects directly, without a proof script.

Here's an example:
{% highlight text %}
Definition HYP (P Q : Prop) : Prop := (P->Q) /\ P.

Definition THM := forall (P Q : Prop), (HYP P Q) -> Q.

Theorem thm_proof : THM.
intros p q.
intro conj.
destruct conj as [imp pp].
apply imp.
apply pp.
Qed.

Definition hypfun P Q : Prop hyp : HYP P Q : Q :=
match hyp with
| conj imp pp => imp pp
end.

Definition thmfun : THM := hypfun
{% endhighlight %}

In this example, we first define the hypothesis `HYP` and the theorem's assertion `THM`, which asserts that `Q` can be derived from the hypothesis. Then we prove the theorem.

What follows is an attempt to rewrite nicely the output of `Print thm_proof`.

The function `hypfun` produces `Q` from the hypothesis. It simply pattern match on the conjunction to extract both sides, and apply the left side to the right side. Since the right side is something of type `P`, and the left side produces something of type `Q` from something of type `P`, the result is what is produced by the right side, which is of type `Q`.

Then `thmfun` simply uses `hypfun`.

This shows that using destruct is equilalent to pattern matching, and apply hypothesese is equivalent to applying functions.

*Proof Scripts*

The command `Show Proof.` can show the proof script in the middle of the proof process.

*Programming with tactics*

Here are three functions on natural defined with tactics. One is the identity, the other is the constant 0, and the third is the successor function.


{% highlight text %}
Definition identity_nat : nat -> nat.
intro n.
apply n.
Qed.

Definition zero_nat : nat -> nat.
intro n.
apply O.
Qed.

Definition successor_nat : nat -> nat.
intro n.
apply S.
apply n.
Qed.

Print identity_nat.
Print zero_nat.
Print successor_nat.
{% endhighlight %}

**Quest Idea**: Describe tactics by their proof script.

## V1 Induction Principles

Every recursive type comes with a `_ind` and `_rect`

{% include SFV1Imp.markdown %}

[Coq]: https://coq.inria.fr/
[documentation]: https://coq.inria.fr/documentation
[sf]: https://softwarefoundations.cis.upenn.edu/
