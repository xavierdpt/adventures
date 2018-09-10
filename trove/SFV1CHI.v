Definition HYP (P Q : Prop) : Prop := (P->Q) /\ P.

Definition THM := forall P Q : Prop, HYP P Q -> Q.

Theorem thm_proof : THM.
Show Proof.
intros p q.
Show Proof.
intro conj.
Show Proof.
destruct conj as [imp pp].
Show Proof.
apply imp.
Show Proof.
apply pp.
Qed.

Definition hypfun (P Q : Prop) (hyp : HYP P Q) : Q :=
match hyp with
| conj imp pp => imp pp
end.

Definition thmfun : THM := hypfun.

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
