Require Import Maps.
Require Import Imp.

Definition aequiv (a1 a2 : aexp) : Prop :=
  forall (st:state),
    aeval st a1 = aeval st a2.

Definition bequiv (b1 b2 : bexp) : Prop :=
  forall (st:state),
    beval st b1 = beval st b2.

Definition cequiv (c1 c2 : com) : Prop :=
  forall (st st' : state),
    (ceval c1 st st') <-> (ceval c2 st  st').

Theorem aequiv_example:
  aequiv (AMinus (AId "X") (AId "X")) (ANum 0).
unfold aequiv.
intro st.
simpl.
induction (st "X"%string).
simpl. reflexivity.
simpl. rewrite IHn. reflexivity.
Qed.

Theorem bequiv_example:
  bequiv (BEq (AMinus (AId "X") (AId "X")) (ANum 0)) BTrue.
unfold bequiv.
intro st.
simpl.
induction (st "X"%string).
simpl. reflexivity.
simpl. rewrite IHn. reflexivity.
Qed.

Theorem skip_left: forall c, cequiv (CSeq CSkip c) c.
intro c.
unfold cequiv.
intros src dst.
split.
intro h.
inversion h as [ | | com1 com2 srcx tmp dstx youpi yapla com1eq srceq dsteq
| | | | ].
