Require Import Coq.Arith.Arith.
Require Import Coq.Bool.Bool.
Require Export Coq.Strings.String.
Require Import Coq.Logic.FunctionalExtensionality.
Require Import Coq.Lists.List.

Definition beq_string x y :=
  if string_dec x y then true else false.

Theorem beq_string_refl : forall s, true = beq_string s s.
unfold beq_string.
Show Proof.
intro s.
Show Proof.
destruct (string_dec s s) as [|h].
trivial.
destruct h. trivial.
Qed.

Theorem beq_string_true_iff : forall x y : string,
  beq_string x y = true <-> x = y.
intros x y.
split.
intro h. unfold beq_string in h. destruct (string_dec x y). assumption. destruct n. inversion h.
intro heq. subst y. symmetry. apply beq_string_refl.
Qed.

Theorem beq_string_false_iff : forall x y : string,
  beq_string x y = false
  <-> x <> y.
intros x y.
split.
intro h.
unfold beq_string in h.
destruct (string_dec x y).
inversion h.
trivial.
intro h.
unfold beq_string.
destruct (string_dec x y).
subst y. destruct h. trivial.
trivial.
Qed.

Theorem false_beq_string : forall x y : string,
   x <> y -> beq_string x y = false.
intros x y.
intro neq.
unfold beq_string.
destruct (string_dec x y).
subst y. destruct neq. trivial. trivial.
Qed.

Definition total_map (A:Type) := string -> A.

Definition t_empty {A:Type} (v : A) : total_map A :=
  (fun _ => v).

Definition t_update {A:Type} (m : total_map A)
                    (x : string) (v : A) :=
  fun x' => if beq_string x x' then v else m x'.

Definition partial_map (A:Type) := total_map (option A).

Definition empty {A:Type} : partial_map A :=
  t_empty None.


Definition update {A:Type} (m : partial_map A)
           (x : string) (v : A) :=
  t_update m x (Some v).

Lemma apply_empty : forall (A: Type) (x: string), @empty A x = None.
trivial.
Qed.

Lemma update_eq : forall A (m: partial_map A) x v,
    (update m x v) x = Some v.
intros.
unfold update.
unfold t_update.
unfold partial_map in m.
unfold beq_string.
destruct (string_dec x x).
trivial.
destruct n. trivial.
Qed.

Theorem update_neq : forall (X:Type) v x1 x2
                       (m : partial_map X),
  x2 <> x1 ->
  (update m x2 v) x1 = m x1.
intros.
unfold update.
unfold t_update.
unfold beq_string.
destruct (string_dec x2 x1).
subst x2. destruct H. trivial.
trivial.
Qed.

Theorem f_equal : forall (A B : Type) (f: A -> B) (x y: A),
  x = y -> f x = f y.
Proof. intros A B f x y eq. rewrite eq. reflexivity. Qed.

Axiom youpi : forall (A B : Type) (f g:A->B), (forall a, f a = g a) -> f = g.

Lemma update_shadow : forall A (m: partial_map A) v1 v2 x,
    (update  (update m x v1) x v2) = (update m x v2).
intros.
unfold update.
unfold t_update.
apply youpi.
intro a.
destruct (beq_string x a);trivial.
Qed.

Theorem update_same : forall X v x (m : partial_map X),
  m x = Some v ->
  (update m x v) = m.
intros.
unfold update.
unfold t_update.
apply youpi.
intro a.
unfold beq_string.
destruct (string_dec x a).
subst a. symmetry. trivial. trivial.
Qed.

Theorem update_permute : forall (X:Type) v1 v2 x1 x2
                                (m : partial_map X),
  x2 <> x1 ->
  (update (update m x2 v2) x1 v1)
  = (update( update m x1 v1) x2 v2).
intros.
unfold update. unfold t_update. unfold beq_string. apply youpi. intro a.
destruct (string_dec x1 a).
destruct (string_dec x2 a).
subst x1 x2. destruct H. trivial.
trivial.
destruct (string_dec x2 a). trivial. trivial.
Qed.


