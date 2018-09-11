Require Export Basics.

Theorem plus_n_O : forall n :nat, n = plus n O.
induction n as [|m h].
Show Proof.
reflexivity.
Show Proof.
simpl. rewrite <- h. reflexivity.
Show Proof.
Qed.

Definition plus_n_O' : forall n : nat, n = plus n O :=
(fun n : nat => nat_ind
  (fun n0 : nat => n0 = plus n0 O)
  eq_refl
  (fun (m : nat) (h : m = plus m O) => eq_ind m
    (fun n0 : nat => S m = S n0)
    eq_refl
    (plus m O)
    h
  )
  n
)
.

Theorem minus_diag : forall n:nat, minus n n = O.
induction n as [|m h].
Show Proof.
reflexivity.
Show Proof.
simpl. assumption.
Show Proof.
Qed.

Definition minus_diag' : forall n:nat, minus n n = O :=
(fun n : nat =>
 nat_ind (fun n0 : nat => minus n0 n0 = O) eq_refl
   (fun (m : nat) (h : minus m m = O) => h) n).

Theorem plus_commute : forall n m : nat, (plus n m) = (plus m n).
induction n.
induction m.
reflexivity.
simpl. rewrite <- IHm. simpl. reflexivity.
induction m. simpl. rewrite IHn. simpl. reflexivity.
simpl. simpl in IHm. rewrite IHn. simpl.  rewrite <- IHm. rewrite <- IHn. reflexivity.
Show Proof.
Qed.


Theorem plus_rearrange : forall n m p q : nat, (plus (plus n m) (plus p q)) = (plus (plus m n) (plus p q)).
intros n m p q.
rewrite (plus_commute n m).
reflexivity.
Show Proof.
Qed.

Theorem plus_assoc : forall n m p : nat, (plus n (plus m p)) = (plus (plus n m) p).
induction n.
reflexivity.
intros m p.
simpl.
rewrite <- IHn.
reflexivity.
Show Proof.
Qed.

Theorem thm : forall n m : nat, n = plus n m -> m = O.
induction n.
intro m. intro h. simpl in h. symmetry. assumption.
intro m.
intro h.
apply IHn.
inversion h.
rewrite <- H0.
rewrite <- H0.
reflexivity.
Show Proof.
Qed.

Theorem thm' : forall a : bool, negb a = false -> a = true.
intros a h.
destruct a.
reflexivity.
simpl in h.
inversion h.
Show Proof.
Qed.

Theorem thma : forall n:nat, n=n.
reflexivity.
Show Proof.
Qed.

Theorem thmb : forall n m:nat, n=m -> (plus O n)=(plus O m).
intros n m heq.
rewrite heq.
reflexivity.
Show Proof.
(*
(fun (n m : nat) (heq : n = m) => eq_ind_r
  (fun n0 : nat => plus O n0 = plus O m)
  eq_refl
  heq
)
*)
Qed.


Theorem thmc : forall n m:nat, n=m -> (plus O n)=(plus O m).
intros n m heq.
apply heq.
Show Proof.
Qed.

Theorem thmd : forall n m:nat, n=m -> (plus O n)=(plus O m).
intros n m heq.
rewrite <- heq.
reflexivity.
Show Proof.
(*
(fun (n m : nat) (heq : n = m) => eq_ind
  n
  (fun m0 : nat => plus O n = plus O m0)
  eq_refl
  m
  heq)
*)
Qed.

Theorem thme : forall (n m: nat) (f:nat->nat), n=m -> f n = f m.
intros n m f heq.
rewrite heq.
reflexivity.
Show Proof.
(*
(fun (n m : nat) (f : nat -> nat) (heq : n = m) =>
 eq_ind_r (fun x : nat => f x = f m) eq_refl heq)
*)
Qed.

Print eq_ind_r.
(*
eq_ind_r = fun (A : Type) (x : A) (P : A -> Prop) (H : P x) (y : A) (H0 : y = x) =>
eq_ind x (fun y0 : A => P y0) H y (eq_sym H0) :
forall (A : Type) (x : A) (P : A -> Prop), P x -> forall y : A, y = x -> P y
*)

Print eq_ind.
(*
eq_ind = fun (A : Type) (x : A) (P : A -> Prop) => eq_rect x P :
forall (A : Type) (x : A) (P : A -> Prop), P x -> forall y : A, x = y -> P y
*)

Print eq_rect.
(*
eq_rect = fun (A : Type) (x : A) (P : A -> Type) (f : P x) (y : A) (e : x = y) =>
match e in (_ = y0) return (P y0) with
| eq_refl => f
end :
forall (A : Type) (x : A) (P : A -> Type),P x -> forall y : A, x = y -> P y
*)

Print eq_refl.

Theorem thmf :
forall (f : nat -> nat) (x:nat) (P:nat->Prop) (H:P x) (m:nat) (H0:m=x) (toto:P m),
P = (fun x : nat => f x = f m) ->
@eq_ind_r nat x P H m H0 = toto.
intros f x P H y H0 toto Ph.
unfold eq_ind_r.
unfold eq_ind.
unfold eq_rect.
subst P.
Admitted.


