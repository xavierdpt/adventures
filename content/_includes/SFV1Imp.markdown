## V1 Simple Imperative Programs

Tacticals `try`, `;` (simple and general form), `repeat`

`Tactic Notation`, LTac primitives, OCaml API

`omega` with `Require Import Coq.omega.Omega`

`clear`, `subst`, `rename`, `assumption`, `contradiction`, `constructor`

`Reserved Notation`

In large Coq developments it is common to see a definition given in both functional and relational styles, plus a lemma stating that the two coincide, allowing further proofs to switch from one point of view to the other at will.

**Quest Idea**: Change the point of view in some "large" development.

`Coercion`, `Bind Scope`, `Infix`, `Open Scope`

The imperative language being defined allow infinite loops, but Coq does not allow potentially infinite recursions.

To solve this, evaluation must be defined as a relation. Then every programs must be proven to evaluate to the corresponding results, infinite recursions will correspond to  infinite proofs, but all attempts at finite computations are on the user's shoulder, i.e. Coq itself will never attempt to perform a computation that may be infinite.




