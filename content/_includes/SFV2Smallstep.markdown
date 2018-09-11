## Volume 2 : Small-Step Operational Semantics

What was done was big-step semantics, called natural semantics by Gilles Kahn.

This style is not very well suited to concurrent programming languages.

Also, supporting undefined behavior requires using Inductive propositions rather than fixpoints.

Now, a command may fail for two different reasons : infinite loop or undefined behavior.

What is desirable is to allow infinite loops but prevent undefined behavior.

Toy language with only constants and addition, with a big-step style evaluator, defined by a Fixpoint and an Inductive relation.

Then the small-step evaluation relation is exposed.

Parenthesis on relations : binary relations, deterministic relation, custom tactic.

Strong progress, normal forms.

Multi-step reduction relation.

Proof that the big step and small step definitions define the same thing.

Small-step version of the Imp language.

Additional command in Imp which launches computations in parallel.

Proof that some example program can terminate with any values.

Small step stack machine.

{% comment %}
Open quests:
{% endcomment %}
