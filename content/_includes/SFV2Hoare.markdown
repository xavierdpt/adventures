## Volume 2 : Hoare Logic Part I

In volume 1, a small programming language was defined, with abstract syntax trees and an evaluation relation which specifies operational semantics.

Properties which were proven include determinism of evaluation, equivalence of functional and relational definitions of arithmetic expression evaluation, guaranteed termination of some programs, correctness of some program transformations, and behavioral equivalence.

Goal of this part is to carry some program verification with Floyd-Hoare Logic.

Floyd-Hoare logic combines a natural way of writing down specifications with a compositional proof technique for proving program correctness.

Assertions.

An Hoare triple (Pre-condition ; command ; Post-condition) specifies that when command is called on a state satisfying the precondition and terminates, then it must satisfy the post condition.

Hoare triples for assignment. 

The `eapply` tactic applies a theorem and replace all the premises that it failed to unify with existential variables.

`eassumption` works like `assumption`, but tries to use existential variables.





{% comment %}
Open quests:
{% endcomment %}
