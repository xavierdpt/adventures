Require Export Poly.

Theorem silly1 : forall n m o p : nat, n=m -> (cons n (cons o nil)) = (cons n (cons p nil)) -> (cons n (cons o nil)) = (cons m (cons p nil)).
intros n m o p eqnat eqlist.
subst n.
assumption.
Show Proof.
Qed.

Theorem silly2 : forall (n m o p : nat), n=m ->
(forall (q r : nat), q=r -> (cons q (cons o nil)) = (cons r (cons p nil))) ->
(cons n (cons o nil)) = (cons m (cons p nil)).
intros n m o p eqnat eqlist.
apply eqlist.
assumption.
Show Proof.
Qed.

Theorem silly2a : forall (n m : nat), (cons n (cons n nil)) = (cons m (cons m nil)) ->
(forall (q r : nat), (cons q (cons q nil)) = (cons r (cons r nil)) -> (cons q nil) = (cons r nil)) ->
(cons n nil) = (cons m nil).
intros n m eqnm eqqr.
apply eqqr.
apply eqnm.
Show Proof.
Qed.

Theorem silly3 : forall (n:nat), true = beq_nat n O -> beq_nat (S(S n)) (S(S O)) = true.
simpl.
intros n h.
symmetry.
apply h.
Show Proof.
Qed.

Theorem trans_eq : forall (X:Type) (n m o : X), n=m->m=o->n=o.
intros X n m o eqnm eqmo.
subst. reflexivity.
Show Proof.
Qed.

Theorem trans_eq_example : forall (a b c d e f : nat),
(cons a (cons b nil)) = (cons c (cons d nil)) ->
(cons c (cons d nil)) = (cons e (cons f nil)) ->
(cons a (cons b nil)) = (cons e (cons f nil)).
intros a b c d e f.
apply trans_eq.
Show Proof.

Theorem S_injective : forall n m : nat, S n = S m -> n = m.
intros n m h.
inversion h.
reflexivity.
Show Proof.
Qed.

Theorem inversion_ex1 : forall n m o : nat, (cons n (cons m nil)) =  (cons o (cons o nil)) -> (cons n nil) = (cons m nil).
intros n m o h.
inversion h as [heq1].
reflexivity.
Show Proof.
Qed.

Theorem inversion_ex2 : forall n m : nat, (cons n nil) = (cons m nil) -> n = m.
intros n m h.
inversion h as [heq].
reflexivity.

Theorem beq_nat_0_l  : forall n, beq_nat O n = true -> n = O.
intros n heq.
destruct n.
trivial.
simpl in heq.
Show Proof.
inversion heq.
Show Proof.
Qed.

Theorem f_equal : forall (A B : Type) (f:A->B) (x y : A), x = y -> f x = f y.
intros A B f x y heq.
subst y.
trivial.
Qed.

Theorem S_inj : forall  (n m : nat) (b : bool), beq_nat (S n) (S m)=b -> beq_nat n m = b.
trivial.
Show Proof.
Qed.

Fixpoint double (n:nat) : nat :=
match n with
| O => O
| S n' => S (S (double n'))
end.

Theorem double_plus_plus : forall n : nat, double n = plus n n.
induction n.
trivial.
simpl.
rewrite plus_commute.
simpl.
rewrite IHn. trivial.
Qed.

Theorem S_eq : forall n m : nat, n=m -> S n = S m.
intros n m heq.
subst m.
trivial.
Show Proof.
Qed.

Theorem S_qe : forall n m : nat, S n = S m -> n = m.
induction n.
destruct m;try(trivial);try (intro h;inversion h).
induction m.
intro h;inversion h.
intro hss.
rewrite <- IHn.
rewrite IHm.
symmetry.
apply IHn.
apply S_eq.


(* This proof is bad for some reason *)
Theorem double_injective : forall n m, double n = double m -> n = m.
induction n.
destruct m.
trivial.
simpl. intro h;inversion h.
destruct m. intro h;inversion h.
intro h.
apply S_eq.
apply IHn.
simpl in h.
apply S_injective.
apply S_injective.
assumption.
Show Proof.
Qed.

Theorem double_injective' : forall n m, double n = double m -> n = m.
intro n.
induction n as [|n' HI].
simpl. intros m eq.
destruct m as [|m']. trivial. inversion eq.
simpl.
intros m eq.
destruct m as [|m'].
inversion eq.
apply f_equal.
apply HI.
inversion eq.
trivial.
Qed.


Theorem double_injective'' : forall n m, double n = double m -> n = m.
induction n as [|n' HI].
intros m eq;destruct m;[trivial|inversion eq].
destruct m as [|m']. intro eq ; inversion eq.
intro h.
apply f_equal.
apply HI.
inversion h as [heq].
trivial.
Show Proof.
Qed.

