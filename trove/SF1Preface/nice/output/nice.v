(** Let's prove a simple theorem **)

Theorem thm : forall P Q:Prop, ((P->Q)/\P)->Q.
intros p q h.
destruct h.
apply H.
assumption.
Qed.
