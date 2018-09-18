Require Import Imp.
Require Import Maps.

Definition Assertion := state -> Prop.

Definition assert_implies (P Q : Assertion) : Prop :=
  forall st, P st -> Q st.

Definition assert_iff (P Q : Assertion) : Prop := assert_implies P Q /\ assert_implies Q P.

Definition hoare_triple
           (P:Assertion) (c:com) (Q:Assertion) : Prop :=
  forall st st',
     ceval c st st' ->
     P st ->
     Q st'.

Theorem hoare_post_true : forall (P Q : Assertion) c,
  (forall st, Q st) ->
  hoare_triple P c Q.
unfold Assertion.
intros P Q.
intro com.
intro hq.
unfold hoare_triple.
intros src dst.
intro heval.
intro psrc.
apply hq.
Qed.

Theorem hoare_pre_false : forall (P Q : Assertion) c,
  (forall st, ~(P st)) ->
  (hoare_triple P c Q).
unfold Assertion.
intros P Q.
intros com hnp.
unfold hoare_triple.
intros src dst.
intro heval.
intro psrc.
apply hnp in psrc. inversion psrc.
Qed.

Definition assn_sub X a P : Assertion :=
  fun (st : state) =>  P (t_update st X (aeval st a) ).

Theorem hoare_asgn : forall Q X a,
  hoare_triple (assn_sub X a Q) (CAss X a) Q.
intros Q X exp.
unfold hoare_triple.
intros src dst.
intro heval.
unfold assn_sub.
intro hq.
inversion heval as [|src1 exp1 n id hevaln heqid heqsrc hupdate | | | | | ].
subst id. subst exp1. subst src1.
subst n.
assumption.
Qed.

Theorem hoare_consequence_pre : forall (P P' Q : Assertion) c,
  hoare_triple P' c Q ->
  assert_implies P P' ->
  hoare_triple P c Q.
intros P Q R.
intro com.
intro hqr.
intro apq.
unfold assert_implies in apq.
unfold hoare_triple.
intros src dst.
intro heval.
intro psrc.
unfold hoare_triple in hqr.
apply (hqr src).
{ assumption. }
{ apply apq. assumption. }
Qed.

Theorem hoare_consequence_post : forall (P Q Q' : Assertion) c,
  (hoare_triple P c Q') ->
  (assert_implies Q' Q) ->
  (hoare_triple P c Q).
unfold hoare_triple.
unfold assert_implies.
intros P Q R.
intro com.
intro hpr.
intro hrq.
intros src dst.
intro heval.
intro psrc.
apply hrq.
apply (hpr src).
{ assumption. }
{ assumption. }
Qed.

Theorem hoare_consequence : forall (P P' Q Q' : Assertion) c,
  hoare_triple P' c Q' ->
  assert_implies P P' ->
  assert_implies Q' Q ->
  hoare_triple P c Q.
intros P Q R S.
intro com.
intros hqs hpq hsr.
unfold hoare_triple.
intros src dst.
intros heval psrc.
unfold hoare_triple in hqs.
unfold assert_implies in hpq, hsr.
apply hsr.
apply (hqs src).
{ assumption. }
{ apply hpq. assumption. }
Qed.

Theorem hoare_skip : forall P,
     (hoare_triple P CSkip P).
intro P.
unfold hoare_triple.
intros src dst.
intro heval.
inversion heval as [ tmp eq srceq dsteq | | | | | | ].
intro;assumption.
Qed.

Theorem hoare_seq : forall P Q R c1 c2,
     hoare_triple Q c2 R ->
     hoare_triple P c1 Q ->
     hoare_triple P (CSeq c1 c2) R.
unfold hoare_triple.
intros P Q R cam cem.
intros hqr hpq.
intros src dst.
intro heval.
intro psrc.
inversion heval as [ | | cam1 cem1 src1 tmp dst1 cameval cemeval cameq srceq dsteq | | | | ].
subst cam1 cem1 src1 dst1.
apply (hqr tmp).
{ assumption. }
{ apply (hpq src).
  { assumption. }
  { assumption. }
}
Qed.

Definition bassn b : Assertion :=
  fun st => (beval st b = true).

Lemma bexp_eval_true : forall b st,
  beval st b = true -> (bassn b) st.
intros exp st.
intro htrue.
unfold bassn. assumption.
Qed.

Lemma bexp_eval_false : forall b st,
  beval st b = false -> ~ ((bassn b) st).
intros exp st hfalse.
unfold bassn.
intro tata.
rewrite hfalse in tata.
inversion tata.
Qed.

Theorem hoare_if : forall P Q b c1 c2,
  hoare_triple (fun st => P st /\ bassn b st) c1 Q ->
  hoare_triple (fun st => P st /\ ~(bassn b st)) c2 Q ->
  hoare_triple P (CIf b c1 c2) Q.
unfold hoare_triple.
intros P Q exp ctrue cfalse.
intro htrue.
intro hfalse.
intros src dst.
intro heval.
intro psrc.
inversion heval as [ | |
| src1 dst1 exp1 ctrue1 cfalse1 hevaltrue  hcevaltrue  expeq srceq dsteq
| src1 dst1 exp1 ctrue1 cfalse1 hevalfalse hcevalfalse expeq srceq dsteq
| | ].
{
  subst dst1 src1 cfalse1 ctrue1 exp1.
  apply (htrue src).
  {
    assumption.
  }
  { split.
    { assumption. }
    { unfold bassn. assumption. }
  }
}
{
  subst dst1 src1 cfalse1 ctrue1 exp1.
  apply (hfalse src).
  {
    assumption.
  }
  { split.
    { assumption. }
    { intro hn. unfold bassn in hn. rewrite hevalfalse in hn. inversion hn. }
  }
}
Qed.

Theorem hoare_while : forall P b c,
  (hoare_triple (fun st => P st /\ bassn b st) c P ->
  (hoare_triple P (CWhile b c) (fun st => P st /\ ~ (bassn b st)))).
  intros P b c Hhoare st st' He HP.
  remember (CWhile b c ) as wcom eqn:Heqwcom.
  induction He;
    try (inversion Heqwcom); subst; clear Heqwcom.
  - (* E_WhileFalse *)
    split. assumption. apply bexp_eval_false. assumption.
  - (* E_WhileTrue *)
    apply IHHe2. reflexivity.
    apply (Hhoare st st'). assumption.
      split. assumption. apply bexp_eval_true. assumption.
Qed.