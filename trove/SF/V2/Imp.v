Require Export Coq.Strings.String.
Require Import Coq.Arith.Arith.

Definition beq_string x y :=
  if string_dec x y then true else false.

Definition total_map (A:Type) := string -> A.

Definition t_update {A:Type} (m : total_map A)
                    (x : string) (v : A) :=
  fun x' => if beq_string x x' then v else m x'.


Definition state := total_map nat.

Inductive aexp : Type :=
  | ANum : nat -> aexp
  | AId : string -> aexp
  | APlus : aexp -> aexp -> aexp
  | AMinus : aexp -> aexp -> aexp
  | AMult : aexp -> aexp -> aexp.

Inductive bexp : Type :=
  | BTrue : bexp
  | BFalse : bexp
  | BEq : aexp -> aexp -> bexp
  | BLe : aexp -> aexp -> bexp
  | BNot : bexp -> bexp
  | BAnd : bexp -> bexp -> bexp.

Inductive com : Type :=
  | CSkip : com
  | CAss : string -> aexp -> com
  | CSeq : com -> com -> com
  | CIf : bexp -> com -> com -> com
  | CWhile : bexp -> com -> com.


Fixpoint aeval (st : state) (a : aexp) : nat :=
  match a with
  | ANum n => n
  | AId x => st x
  | APlus a1 a2 => (aeval st a1) + (aeval st a2)
  | AMinus a1 a2 => (aeval st a1) - (aeval st a2)
  | AMult a1 a2 => (aeval st a1) * (aeval st a2)
  end.

Fixpoint beval (st : state) (b : bexp) : bool :=
  match b with
  | BTrue => true
  | BFalse => false
  | BEq a1 a2 => beq_nat (aeval st a1) (aeval st a2)
  | BLe a1 a2 => leb (aeval st a1) (aeval st a2)
  | BNot b1 => negb (beval st b1)
  | BAnd b1 b2 => andb (beval st b1) (beval st b2)
  end.

Inductive ceval : com -> state -> state -> Prop :=
  | E_Skip : forall st,
      (ceval CSkip st st)
  | E_Ass : forall st a1 n x,
      aeval st a1 = n ->
      (ceval (CAss x a1) st (t_update st x n ))
  | E_Seq : forall c1 c2 st st' st'',
      (ceval c1 st st') ->
      (ceval c2 st' st'') ->
      (ceval (CSeq c1 c2) st st'')
  | E_IfTrue : forall st st' b c1 c2,
      beval st b = true ->
      (ceval c1 st st') ->
      (ceval (CIf b c1 c2) st st')
  | E_IfFalse : forall st st' b c1 c2,
      beval st b = false ->
      (ceval c2 st st') ->
      (ceval (CIf b c1 c2) st st')
  | E_WhileFalse : forall b st c,
      beval st b = false ->
      (ceval (CWhile b c) st st)
  | E_WhileTrue : forall st st' st'' b c,
      beval st b = true ->
      (ceval c st st') ->
      (ceval (CWhile b c) st' st'') ->
      (ceval (CWhile b c) st st'')
.

Definition aequiv (a1 a2 : aexp) : Prop :=
  forall (st:state),
    aeval st a1 = aeval st a2.

Definition bequiv (b1 b2 : bexp) : Prop :=
  forall (st:state),
    beval st b1 = beval st b2.

Definition cequiv (c1 c2 : com) : Prop :=
  forall (st st' : state),
    (ceval c1 st st') <-> (ceval c2 st st').


Lemma refl_aequiv : forall (a : aexp), aequiv a a.
intro a.
red.
intro st.
reflexivity.
Qed.

Lemma sym_aequiv : forall (a1 a2 : aexp), aequiv a1 a2 -> aequiv a2 a1.
intros a b.
intro hab.
red.
red in hab.
intro st.
symmetry.
apply hab.
Qed.

Lemma trans_aequiv : forall (a1 a2 a3 : aexp),  aequiv a1 a2 -> aequiv a2 a3 -> aequiv a1 a3.
intros a b c.
intros hab hbc.
red.
intro st.
red in hbc.
red in hab.
rewrite (hab st).
trivial.
Qed.


Lemma refl_bequiv : forall (b : bexp), bequiv b b.
intro b.
red.
intro st.
trivial.
Qed.

Lemma sym_bequiv : forall (b1 b2 : bexp), bequiv b1 b2 -> bequiv b2 b1.
intros a b.
intro hab.
red.
red in hab.
intro st.
symmetry.
trivial.
Qed.

Lemma trans_bequiv : forall (b1 b2 b3 : bexp),  bequiv b1 b2 -> bequiv b2 b3 -> bequiv b1 b3.
intros a b c.
intros hab hbc.
red.
red in hab, hbc.
intro st.
rewrite (hab st).
trivial.
Qed.

Lemma refl_cequiv : forall (c : com), cequiv c c.
intro c.
red.
intros s u.
split;try(intro hsu;destruct c;trivial).
Qed.

Lemma sym_cequiv : forall (c1 c2 : com), cequiv c1 c2 -> cequiv c2 c1.
Admitted.

Lemma trans_cequiv : forall (c1 c2 c3 : com),
  cequiv c1 c2 -> cequiv c2 c3 -> cequiv c1 c3.
Admitted.

Theorem CAss_congruence : forall i a1 a1', aequiv a1 a1' ->  cequiv (CAss i a1) (CAss i a1').
Show Proof.
intros i a b.
Show Proof.
intro hab.
Show Proof.
red.
Show Proof.
intros s u.
Show Proof.
split.
Show Proof.
intro hsu.
Show Proof.
inversion hsu.
Show Proof.
rewrite <- H3.
Show Proof.
apply E_Ass.
Show Proof.
red in hab.
Show Proof.
rewrite hab.
Show Proof.
trivial.
Show Proof.
intro hbsu.
inversion hbsu.
subst.
apply E_Ass.
rewrite hab.
trivial.
Show Proof.
Qed.
