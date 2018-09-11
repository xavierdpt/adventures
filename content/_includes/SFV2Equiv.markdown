## Volume 2 : Program Equivalence

Arithmetic and boolean expressions are equivalence when they evaluate to the same values.

Two commands are equivalent if one command terminates on some state if and only iff the other does.

Example: Skipping can be removed.

Example: Skipping can be added.

Example: Conditional with `true` can be optimized out.

Example: Conditional which evaluates to `true` can be optimized out.

Example: Conditionals can be swapped when the condition is negated.

Similar theorems apply to while loops.

Example : When the guard is equivalent to true, the while loop never terminates.

Example : Loop unrolling

The three relations defined (arithmetic, boolean, commands) are equivalence relations.

Congruences properties must be proved for every constructor (i.e. CIf, CSeq, ...)

Definition of sound program transformation.

Constant folding is a sound transformation.

One source of nondeterminism is variables initialized with arbitrary values.

{% comment %}
Open quests:
{% endcomment %}
