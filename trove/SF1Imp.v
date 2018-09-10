Require Import Coq.Bool.Bool.
Require Import Coq.Arith.Arith.
Require Import Coq.Arith.EqNat.
Require Import Coq.omega.Omega.
Require Import Coq.Lists.List.
Require Export Coq.Strings.String.
Import ListNotations.

Definition beq_string x y :=
  if string_dec x y then true else false.

Definition total_map (A:Type) := string -> A.

Definition t_empty {A:Type} (v : A) : total_map A := (fun _ => v).

Definition t_update {A:Type} (m : total_map A) (x : string) (v : A) :=
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
      ceval CSkip st  st
  | E_Ass : forall st a1 n x,
      aeval st a1 = n ->
      ceval (CAss x a1) st (t_update st x n)
  | E_Seq : forall c1 c2 st st' st'',
      ceval c1 st st' ->
      ceval c2 st' st'' ->
      ceval (CSeq c1 c2) st st''
  | E_IfTrue : forall st st' b c1 c2,
      beval st b = true ->
      ceval c1 st st' ->
      ceval (CIf b c1 c2) st st'
  | E_IfFalse : forall st st' b c1 c2,
      beval st b = false ->
      ceval c2 st st' ->
      ceval (CIf b c1 c2) st st'
  | E_WhileFalse : forall b st c,
      beval st b = false ->
      ceval (CWhile b c) st st
  | E_WhileTrue : forall st st' st'' b c,
      beval st b = true ->
      ceval c st st' ->
      ceval (CWhile b c) st' st'' ->
      ceval (CWhile b c) st st''
.

Fixpoint opt0p (a:aexp) : aexp :=
  match a with
  | ANum n => ANum n
  | AId x => AId x
  | APlus (ANum 0) e2 => opt0p e2
  | APlus e1 e2 => APlus (opt0p e1) (opt0p e2)
  | AMinus e1 e2 => AMinus (opt0p e1) (opt0p e2)
  | AMult e1 e2 => AMult (opt0p e1) (opt0p e2)
  end.

Theorem opt0p_sound_1: forall a st, aeval st (opt0p a) = aeval st a.
intros a st.
induction a.
reflexivity.
reflexivity.
rename a1 into a. rename a2 into b. rename IHa1 into ha. rename IHa2 into hb.
destruct a.
destruct n.
simpl.
rewrite hb.
reflexivity.
simpl.
rewrite hb.
reflexivity.
simpl. rewrite hb. reflexivity.
simpl. simpl in ha. rewrite ha. rewrite hb. reflexivity.
simpl. simpl in ha. rewrite ha. rewrite hb. reflexivity.
simpl. simpl in ha. rewrite ha. rewrite hb. reflexivity.
rename a1 into a. rename a2 into b. rename IHa1 into ha. rename IHa2 into hb.
simpl. simpl in ha. rewrite ha. rewrite hb. reflexivity.
rename a1 into a. rename a2 into b. rename IHa1 into ha. rename IHa2 into hb.
simpl. simpl in ha. rewrite ha. rewrite hb. reflexivity.
Qed.

Theorem opt0p_sound_2: forall a st, aeval st (opt0p a) = aeval st a.
intros a st.
induction a as [n | x | a ha b hb | a ha b hb | a ha b hb ];
try (trivial);
try (simpl; rewrite ha; rewrite hb; reflexivity).
destruct a;
try (simpl; simpl in ha; rewrite ha; rewrite hb; reflexivity);
try (simpl; rewrite hb; reflexivity).
destruct n; try(simpl; rewrite hb; reflexivity).
Qed.

Definition empty := t_empty 0.
Definition set st (id:string) (val:nat) := t_update st id val.

Example ceval_example1: (ceval
(CSeq
  (CAss "X" (ANum 2))
  (CIf (BLe (AId "X") (ANum 1))
    (CAss "Y" (ANum 3))
    (CAss "Z" (ANum 4))
  )
)
empty
(set (set empty "X" 2) "Z" 4)).
apply E_Seq with (set empty "X" 2).
apply E_Ass. trivial.
apply E_IfFalse. trivial.
apply E_Ass. trivial.
Qed.




