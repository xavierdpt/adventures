## Volume 1 : Preface

Like other formal softwares such as Mathematica, Maxima or Sage, Coq features the ability of converting the raw Coq scripts into nice documentation artefacts. 

We provide a minimalist example of how to do that in [the trove][trove_coqdoc].

Software Foundations is about Coq in particular, and automated theorems in general. Such tools include SAT solvers, SMT solvers and model checkers.

Beside Coq, other interactive proof assistants include Isabelle, Twelf, ACL2 and PVS.

The coq system includes:
* a proof-checker
* a large library of common definitions and lemmas
* tactics for constructing complex proofs semi-automatically
* a special-purpose programming language for defining new tactics called LTac

Coq has been used to
* To check the security of the JavaCard platform
* Formal specifications of the x86 and LLVM instruction sets
* Formal specifications of the C programming languages and others.

Coq has been used to build:
* CompCert, a fully-verified optimizing compiler for C
* CertiKos, a fully verified hypervisor
* Proving the correctness of subtle algorithms involving floating point numbers
* CertiCrypt, an environment for reasoning about the security of cryptographic algorithms
* verified implementations of the open-source RISC-V processor

The Ynot system embeds "relational Hoare reasoning" in Coq.

Coq has been used to develop the first formally verified proof of the 4-color theorem.

Coq has been used to formalize a proof the Feit-Thompson Theorem, which is the first major step in the classification of finite simple groups.

Beside coq, other functional programming languages include Haskell, OCaml, Standard ML, F#, Scala, Scheme, Racket, Common Lisp, Clojure and Erlang.

Functional programming is well-suited to formal methods, because pure functions have no side effects, which make them easier to reason with and parallelize.

Two Coq IDEs are Proof General for Emacs and CoqIDE.

{% comment %}
Open quests:
* Experiment with a SAT solver.
* Experiment with an SMT solver.
* Experiment with a model checker.
* Experiment with Isabelle.
* Experiment with Twelf.
* Experiment with ACL2.
* Experiment with PVS.
* Define a custom tactic in LTac and use it.
* Define a custom tactic in the OCaml API and use it.
* Investigate JavaCard.
* Investigate LLVM.
* Investigate the formal specification of some programming language.
* Investigate CompCert.
* Investigate CertiKos.
* Investigate CertiCrypt.
* Investigate Ynot
* Investigate the Feit-Thompson Theorem
* Do something in Haskell
* Do something in Ocaml
* Do something in Standard ML
* Do something in F#
* Do something in Scala
* Do something in Racket
* Do something in Common Lisp
* Do something in Clojure
* Do something in Erlang
* Write about lambda-calculus
* Write about the Map-Reduce idiom in Hadoop
* Experiment with Emacs, before experimenting with Proog General

Completed quests:
* Create a nice Coq document about something. : Done :)
{% endcomment %}
[trove_coqdoc]: https://github.com/xavierdpt/adventures/tree/master/trove/SF1Preface/nice
