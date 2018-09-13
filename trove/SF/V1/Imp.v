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
intros c.

 (* We proceed by induction on the command *)
induction c as [
(* Skip *)
|
(* Assignment *) str exp
|
(* Sequences *) c1 eq_c1 c2 eq_c2
|
(* Conditionals *) exp c1 c1_eq c2 c2_eq
|
(* Loops *) exp c c_eq
].

(* First case is Skip *)
intros src dst1 dst2 h1 h2.
(* Using inversions on ceval for h1 and h2 leave only the cases for CSkip *)
inversion h1 as [src1 useless1 src1eq dst1eq| | | | | | ];
inversion h2 as [src2 useless2 src2eq dst2eq| | | | | | ].
(* Now for some cleanup *)
clear useless1 useless2.
subst src1 dst1 src2 dst2.
(* And we get to equality *)
reflexivity.

(* Now is Assignment *)
(* We should have introduced these properly in the induction step *)
intros src dst1 dst2 h1 h2.
inversion_clear h1 as [ | src1 exp1 n1 str1 src_exp_n1 str1eq src1eq src_str_n1_dst1 | | | | | ];
inversion_clear h2 as [ | src2 exp2 n2 str2 src_exp_n2 str2eq src2eq src_str_n2_dst2 | | | | | ].
(* Now we use the fact that n1 and n2 are actually the same things *)
rewrite <- src_exp_n1.
rewrite <- src_exp_n2.
(* And we're done *)
reflexivity.

(* We're now dealing with the sequence commands *)
(* Then some intros *)
intros src dst1 dst2 h1 h2.
(* Then the inversions *)
inversion_clear h1 as  [ | | c1_1 c2_1 src_1  tmp1 dst1_1 src_to_tmp1 tmp1_to_dst1 c2_eq1 src1eq dst11eq | | | | ];
inversion_clear h2 as  [ | | c1_2 c2_2 src_2  tmp2 dst1_2 src_to_tmp2 tmp2_to_dst2 c2_eq2 src2eq dst12eq | | | | ].
(* Now is where the magic happens *)
(* We first assert that dst1 and dst2 are equals using eq_c2 *)
apply (eq_c2 tmp1 dst1 dst2).
(* This require proving that we can go with c2 from tmp1 to dst1, and from tmp1 to dst2*)
(* The fact that we can go from tmp1 to dst1 is true by assumption *)
 assumption.
(* But the fact that we can go from tmp1 to dst2 is less obvious *)
(* So we use eq_c2 to rewrite dst2 into dst1 *)
(* This leaves the current goal in a nice form, but introduce the obligation to prove we can go from tmp2 to dst1 and from tmp2 to dst2 *)
rewrite <- (eq_c2 tmp2 dst1 dst2).
(* The nice form is true by assumption *) assumption.
(* To prove that we can go from tmp2 to dst1 through c2, we rewrite tmp2 into tmp1 with eq_c1 *)
(* This leaves the current goal in a nice form, but introduce the obligation to prove that we can go with c1 from src to tmp2 and from src to tmp1 *)
rewrite (eq_c1 src tmp2 tmp1).
(* This is the nice form *) assumption.
(* src to tmp2 is in the assumptions *) assumption.
(* src to tmp1 is in the assumptions *) assumption.
(* and tmp2 to dst2 is in the assumptions *)assumption.

(* We're now dealing with conditionals *)
intros src dst1 dst2.
intros h1 h2.
(* Here each inversions yields two cases, which make for 4 cases in total *)
inversion_clear h1 as [ | |
| src1 dst1_1 exp_1 c1_1 c2_1 src_exp_true_1  c1_src1_dst1 exp1_eq src1_eq dst1_1_eq
| src1 dst1_1 exp_1 c1_1 c2_1 src_exp_false_1 c1_src1_dst1 exp1_eq src1_eq dst1_1_eq
| | ];
inversion_clear h2 as [ | |
| src2 dst1_2 exp_2 c1_2 c2_2 src_exp_true_2  c1_src2_dst2 exp2_eq src2_eq dst1_2_eq
| src2 dst1_2 exp_2 c1_2 c2_2 src_exp_false_2  c1_src2_dst2 exp2_eq src2_eq dst1_2_eq
| | ].
(* First case goes through c1, because the condition is true *)
apply (c1_eq src dst1 dst2). assumption. assumption.
(* Second case is nonsense *)
rewrite src_exp_false_2 in src_exp_true_1. inversion src_exp_true_1.
(* Third case is nonsense *)
rewrite src_exp_true_2 in src_exp_false_1. inversion src_exp_false_1.
(* And fourth case goes through c2, because the condition is false *)
apply (c2_eq src dst1 dst2). assumption. assumption.

(* We're now left with dealing with loops *)
intros src dst1 dst2.
intros h1 h2.
inversion h1;inversion h2.
subst dst1. subst dst2. reflexivity.
subst dst1. rewrite H3 in H6. inversion H6.
subst dst2. rewrite H1 in H10. inversion H10.

subst. rename st' into tmp1. rename st'0 into tmp2.

(* Stuck ? *)
Abort.

Theorem ceval_deterministic: forall c st st1 st2,
     (ceval c st st1) ->
     (ceval c st st2) ->
     st1 = st2.
intros c src dst1 dst2 h1 h2.
generalize dependent dst2.
induction h1.
intros dst2 hskip.
inversion_clear hskip. reflexivity.
intros dst2 hass.
inversion_clear hass. subst. reflexivity.
intros dst1 hseq. inversion_clear hseq.
rename st into s1.
rename st'0 into s2.
rename st'' into s3.
apply (IHh1_2 dst1).
rewrite (IHh1_1 s2). assumption. assumption.
intros.
inversion_clear h2.
apply IHh1. assumption.
rewrite H in H0. inversion H0.
intros. inversion_clear h2.
rewrite H0 in H. inversion H.
apply IHh1. assumption.
intros. inversion_clear h2. reflexivity. rewrite H0 in H. inversion H.

rename st into s1.
rename b into exp.
rename st' into s2.
rename st'' into s3.

intro s2'.
intro h_s1_s2'.
rename s1 into sa.
rename s2 into sb1.
rename s2' into sb2.
rename s3 into sc.
apply IHh1_2.
rewrite (IHh1_1 sa). assumption.
Abort.

Theorem ceval_deterministic: forall c st st1 st2,
     (ceval c st st1) ->
     (ceval c st st2) ->
     st1 = st2.
  intros c st st1 st2 E1 E2.
  generalize dependent st2.
  induction E1;
           intros st2 E2; inversion E2; subst.
  - (* E_Skip *) reflexivity.
  - (* E_Ass *) reflexivity.
  - (* E_Seq *)
    assert (st' = st'0) as EQ1.
    { (* Proof of assertion *) apply IHE1_1; assumption. }
    subst st'0.
    apply IHE1_2. assumption.
  - (* E_IfTrue, b1 evaluates to true *)
      apply IHE1. assumption.
  - (* E_IfTrue,  b1 evaluates to false (contradiction) *)
      rewrite H in H5. inversion H5.
  - (* E_IfFalse, b1 evaluates to true (contradiction) *)
    rewrite H in H5. inversion H5.
  - (* E_IfFalse, b1 evaluates to false *)
      apply IHE1. assumption.
  - (* E_WhileFalse, b1 evaluates to false *)
    reflexivity.
  - (* E_WhileFalse, b1 evaluates to true (contradiction) *)
    rewrite H in H2. inversion H2.
  - (* E_WhileTrue, b1 evaluates to false (contradiction) *)
    rewrite H in H4. inversion H4.
  - (* E_WhileTrue, b1 evaluates to true *)
      assert (st' = st'0) as EQ1.
      { (* Proof of assertion *) apply IHE1_1. assumption. }
      subst st'0.
      apply IHE1_2. assumption. Qed.