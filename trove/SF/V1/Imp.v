Require Import Coq.Bool.Bool.
Require Import Coq.Arith.Arith.
Require Import Coq.Arith.EqNat.
Require Import Coq.omega.Omega.
Require Import Coq.Lists.List.
Require Import Maps.

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

Fixpoint aeval (st:state) (a : aexp) : nat :=
  match a with
  | ANum n => n
  | AId x => st x
  | APlus a1 a2 => (aeval st a1) + (aeval st a2)
  | AMinus a1 a2 => (aeval st a1) - (aeval st a2)
  | AMult a1 a2 => (aeval st a1) * (aeval st a2)
  end.

Fixpoint beval (st:state) (b : bexp) : bool :=
  match b with
  | BTrue => true
  | BFalse => false
  | BEq a1 a2 => beq_nat (aeval st a1) (aeval st a2)
  | BLe a1 a2 => leb (aeval st a1) (aeval st a2)
  | BNot b1 => negb (beval st b1)
  | BAnd b1 b2 => andb (beval st b1) (beval st b2)
  end.


Fixpoint optimize_0plus (a:aexp) : aexp :=
  match a with
  | ANum n =>
      ANum n
  | AId n =>
      AId n
  | APlus (ANum 0) e2 =>
      optimize_0plus e2
  | APlus e1 e2 =>
      APlus (optimize_0plus e1) (optimize_0plus e2)
  | AMinus e1 e2 =>
      AMinus (optimize_0plus e1) (optimize_0plus e2)
  | AMult e1 e2 =>
      AMult (optimize_0plus e1) (optimize_0plus e2)
  end.

Theorem optimize_0plus_sound: forall st a,
  aeval st (optimize_0plus a) = aeval st a.
induction a;try(simpl; simpl in IHa1; rewrite IHa1; rewrite IHa2; trivial);try(simpl; trivial).
  destruct a1;try(simpl; simpl in IHa1; rewrite IHa1; rewrite IHa2; trivial).
    destruct n;[simpl; assumption|simpl; rewrite IHa2; trivial].
simpl.
rewrite <- IHa2.
reflexivity.
Qed.

Inductive aevalR : aexp -> nat -> state -> Prop :=
  | E_ANum : forall (st:state) (n: nat),
      aevalR (ANum n) n st
  | E_AId : forall (st:state) (s: string),
      aevalR (AId s) (st s) st
  | E_APlus : forall (st:state) (e1 e2: aexp) (n1 n2: nat),
      aevalR e1 n1 st ->
      aevalR e2 n2 st ->
      aevalR (APlus e1 e2) (n1 + n2) st
  | E_AMinus: forall (st:state) (e1 e2: aexp) (n1 n2: nat),
      aevalR e1 n1 st ->
      aevalR e2 n2 st ->
      aevalR (AMinus e1 e2) (n1 - n2) st
  | E_AMult : forall (st:state) (e1 e2: aexp) (n1 n2: nat),
      aevalR e1 n1 st ->
      aevalR e2 n2 st ->
      aevalR (AMult e1 e2) (n1 * n2) st.

Theorem aeval_iff_aevalR : forall st a n,
  (aevalR a n st) <-> aeval st a = n.
split.
intro H.
induction H.
simpl. trivial.
simpl. trivial.
rewrite <- IHaevalR1.
rewrite <- IHaevalR2.
simpl. reflexivity.
rewrite <- IHaevalR1.
rewrite <- IHaevalR2.
simpl. reflexivity.
rewrite <- IHaevalR1.
rewrite <- IHaevalR2.
simpl. reflexivity.
generalize dependent n.
induction a.
simpl. intros. subst. apply E_ANum.
simpl. intros. subst. apply E_AId.
intros.
rewrite <- H. 
apply E_APlus.
apply IHa1. reflexivity.
apply IHa2. reflexivity.
intros. rewrite <- H. simpl. apply E_AMinus. apply IHa1. reflexivity. apply IHa2. reflexivity.
intros. rewrite <- H. simpl. apply E_AMult. apply IHa1. reflexivity. apply IHa2. reflexivity.
Qed.

Inductive ceval : com -> state -> state -> Prop :=
  | E_Skip : forall st,
      (ceval CSkip st st)
  | E_Ass : forall st a1 n x,
      aeval st a1 = n ->
      (ceval  (CAss x a1) st (t_update st x n))
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
      (ceval (CWhile b c) st st'').

Theorem ceval_deterministic: forall c st st1 st2,
     (ceval c st st1) ->
     (ceval c st st2) ->
     st1 = st2.
induction c.
intros.
inversion H.
subst st1 st0.
inversion H0.
reflexivity.
intros.
inversion H.
inversion H0.
subst st0.
subst x0.
subst a0.
subst st3.
subst a1.
subst x.
subst n0.
rewrite H5.
reflexivity.
intros.
inversion H0.
inversion H.
subst.
apply (IHc2 st' st1 st2).
rewrite (IHc2 st'0 st1 st2). assumption. assumption.
rewrite (IHc1 st st'0 st').
assumption.
assumption.
assumption.
assumption.
intros.
inversion H.
inversion H0.
subst.
destruct (beval st b).
apply (IHc1 st st1 st2). assumption. assumption.
inversion H13.
subst.
rewrite H6 in H13. inversion H13.
subst. 
apply (IHc2 st st1 st2). assumption. 
inversion H0. subst. rewrite H8 in H6. inversion H6.
subst. assumption.
intros.
inversion H;inversion H0;subst;destruct (beval st2 b);try(reflexivity).
inversion H5. rewrite H8 in H2. inversion H2. inversion H5. rewrite H8 in H2. inversion H2. inversion H12. inversion H3.
apply (IHc st st1 st2).
