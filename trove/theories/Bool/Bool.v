Definition Is_true (b:bool) :=
  match b with
    | true => True
    | false => False
  end.

Lemma bool_dec : forall b1 b2 : bool, {b1 = b2} + {b1 <> b2}.
Proof.
intros a b.
destruct a;destruct b.
left. reflexivity.
right. discriminate.
right. discriminate.
left. reflexivity.
Show Proof.
Defined.

Lemma diff_true_false : true <> false.
Proof.
discriminate.
Show Proof.
Print False_ind.
Qed.

Lemma diff_false_true : false <> true.
Proof.
  discriminate.
Qed.

Lemma eq_true_false_abs : forall b:bool, b = true -> b = false -> False.
Proof.
intro b.
intro btrue.
subst b.
intro h.
discriminate.
Show Proof.
Qed.

Lemma not_true_is_false : forall b:bool, b <> true -> b = false.
Proof.
destruct b.
intro h.
apply False_ind.
apply h. reflexivity.
intro b. reflexivity.
Show Proof.
Qed.

Lemma not_false_is_true : forall b:bool, b <> false -> b = true.
Proof.
intro b.
intro h.
unfold not in h.
destruct b.
reflexivity.
apply False_ind.
apply h. reflexivity.
Qed.

Lemma not_true_iff_false : forall b, b <> true <-> b = false.
Proof.
unfold iff. unfold not.
destruct b.
split. intro h. apply False_ind. apply h. apply eq_refl.
intro h. intro eq. discriminate.
split. intro h. reflexivity.
intro h. intro hft. discriminate.
Show Proof.
Qed.

Lemma not_false_iff_true : forall b, b <> false <-> b = true.
Proof.
unfold iff. unfold not.
destruct b;split; intros;try(discriminate);try(reflexivity).
contradiction.
Qed.

Definition leb (b1 b2:bool) :=
  match b1 with
    | true => b2 = true
    | false => True
  end.

Lemma leb_implb : forall b1 b2, leb b1 b2 <-> implb b1 b2 = true.
Proof.
unfold implb. unfold leb. unfold iff.
intros a b ; destruct a;destruct b;split;try(reflexivity);try(intro;discriminate).
Qed.

Definition eqb (b1 b2:bool) : bool :=
  match b1, b2 with
    | true, true => true
    | true, false => false
    | false, true => false
    | false, false => true
  end.

Lemma eqb_subst :
  forall (P:bool -> Prop) (b1 b2:bool), eqb b1 b2 = true -> P b1 -> P b2.
Proof.
unfold eqb. intros P a b.
destruct a;destruct b;intros heq pb;try(assumption);try(discriminate).
Qed.

Lemma eqb_reflx : forall b:bool, eqb b b = true.
Proof.
intro b;destruct b;reflexivity.
Qed.

Lemma eqb_prop : forall a b:bool, eqb a b = true -> a = b.
Proof.
intros a b. unfold eqb. destruct a;destruct b;try(reflexivity);intros;try(assumption);try(symmetry;assumption).
Qed.

Lemma eqb_true_iff : forall a b:bool, eqb a b = true <-> a = b.
Proof.
unfold iff. unfold eqb.
intros a b.
destruct a;destruct b;split;intros;try(reflexivity);try(assumption);try(symmetry;assumption).
Qed.

Lemma eqb_false_iff : forall a b:bool, eqb a b = false <-> a <> b.
Proof.
unfold eqb. unfold not.
unfold iff.
intros a b;destruct a;destruct b;split;intros;try(discriminate);try(reflexivity);try(contradiction).
Qed.

Definition ifb (b1 b2 b3:bool) : bool :=
  match b1 with
    | true => b2
    | false => b3
  end.


(****************************)
(** * De Morgan laws          *)
(****************************)

Lemma negb_orb : forall b1 b2:bool, negb (orb b1 b2) = (andb (negb b1) (negb b2)).
Proof.
intros a b.
unfold negb. unfold orb. unfold andb.
destruct a;destruct b;reflexivity.
Qed.

Lemma negb_andb : forall b1 b2:bool, negb (andb b1 b2) = orb (negb b1) (negb b2).
Proof.
unfold negb. unfold andb. unfold orb.
intros a b;destruct a;destruct b;reflexivity.
Show Proof.
Qed.

Lemma negb_involutive : forall b:bool, negb (negb b) = b.
Proof.
intro b;destruct b;reflexivity.
Qed.

Lemma negb_involutive_reverse : forall b:bool, b = negb (negb b).
Proof.
intro b;destruct b;reflexivity.
Qed.

Lemma negb_sym : forall b b':bool, b' = negb b -> b = negb b'.
Proof.
intros a b;unfold negb;destruct a;destruct b;intros;try(assumption);reflexivity.
Qed.

Lemma no_fixpoint_negb : forall b:bool, negb b <> b.
Proof.
intro b;unfold negb;unfold not;intros;destruct b;discriminate.
Qed.

Lemma eqb_negb1 : forall b:bool, eqb (negb b) b = false.
Proof.
intro b;unfold eqb;unfold negb;destruct b;reflexivity.
Qed.

Lemma eqb_negb2 : forall b:bool, eqb b (negb b) = false.
Proof.
unfold eqb;unfold negb;intro b;destruct b;reflexivity.
Qed.

Lemma if_negb :
  forall (A:Type) (b:bool) (x y:A),
    (if negb b then x else y) = (if b then y else x).
Proof.
intros A b x y.
unfold negb.
destruct b;reflexivity.
Qed.

Lemma negb_true_iff : forall b, negb b = true <-> b = false.
Proof.
intro b;unfold iff;unfold negb.
destruct b;split;intros;try(symmetry;assumption);try(reflexivity).
Qed.

Lemma negb_false_iff : forall b, negb b = false <-> b = true.
Proof.
unfold iff;unfold negb.
intro b;destruct b;split;intros;try(reflexivity);try(symmetry;assumption).
Qed.

Lemma orb_true_iff :
  forall b1 b2, orb b1 b2 = true <-> b1 = true \/ b2 = true.
Proof.
unfold iff;unfold orb.
intros a b;destruct a;destruct b;split;intros;try(reflexivity);try(right;reflexivity);try(left;reflexivity);try(right;assumption).
inversion H;assumption.
Qed.

Lemma orb_false_iff :
  forall b1 b2, orb b1 b2 = false <-> b1 = false /\ b2 = false.
Proof.
unfold iff. unfold orb.
intros a b;destruct a;destruct b;split;intros;try(split);try(assumption);try(reflexivity).
inversion H;assumption.
inversion H;try(discriminate).
inversion H;try(discriminate).
Qed.

Lemma orb_true_elim :
  forall b1 b2:bool, (orb b1 b2) = true -> {b1 = true} + {b2 = true}.
Proof.
intros a b.
unfold orb.
destruct a;destruct b;intros;try(left;reflexivity);try(right;reflexivity);try(right;assumption).
Defined.

Lemma orb_prop : forall a b:bool, (orb a b) = true -> a = true \/ b = true.
Proof.
unfold orb.
intros a b;destruct a;destruct b;intros;try(right;reflexivity);try(left;reflexivity).
left;assumption.
Qed.

Lemma orb_true_intro :
  forall b1 b2:bool, b1 = true \/ b2 = true -> orb b1 b2 = true.
Proof.
unfold orb.
intros a b;destruct a;destruct b;intros;try(reflexivity).
inversion H;assumption.
Qed.

Lemma orb_false_intro :
  forall b1 b2:bool, b1 = false -> b2 = false -> orb b1 b2 = false.
Proof.
unfold orb.
intros a b;destruct a;destruct b;intros;try(reflexivity);try(assumption).
Qed.

Lemma orb_false_elim :
  forall b1 b2:bool, orb b1 b2 = false -> b1 = false /\ b2 = false.
Proof.
unfold orb.
intros a b;destruct a;destruct b;intros;split;try(reflexivity);try(assumption).
Qed.

Lemma orb_diag : forall b, orb b b = b.
Proof.
destruct b;reflexivity.
Qed.

Lemma orb_true_r : forall b:bool, orb b true = true.
Proof.
intro b;destruct b;reflexivity.
Qed.


Lemma orb_true_l : forall b:bool, orb true b = true.
Proof.
intro b;destruct b;reflexivity.
Qed.

Lemma orb_false_r : forall b:bool, orb b false = b.
Proof.
intro b;destruct b;reflexivity.
Qed.

Lemma orb_false_l : forall b:bool, orb false b = b.
Proof.
intro b;destruct b;reflexivity.
Qed.

Lemma orb_negb_r : forall b:bool, orb b (negb b) = true.
Proof.
intro b;destruct b;reflexivity.
Qed.

Lemma orb_comm : forall b1 b2:bool, orb b1 b2 = orb b2 b1.
Proof.
intros a b;destruct a;destruct b;reflexivity.
Qed.

Lemma orb_assoc : forall b1 b2 b3:bool, orb b1 (orb b2 b3) = orb (orb b1 b2) b3.
Proof.
intros a b c;destruct a;destruct b;destruct c;reflexivity.
Qed.

Lemma andb_true_iff :
  forall b1 b2:bool, andb b1 b2 = true <-> b1 = true /\ b2 = true.
Proof.
unfold iff,andb.
intros a b;destruct a;destruct b;split;intros;try(split);try(reflexivity);try(assumption).
inversion H;discriminate.
inversion H;discriminate.
inversion H;assumption.
Qed.

Lemma andb_false_iff :
  forall b1 b2:bool, andb b1 b2 = false <-> b1 = false \/ b2 = false.
Proof.
unfold iff, andb.
intros a b;destruct a;destruct b;split;intros;try(left;assumption);try(right;assumption);try(reflexivity).
inversion H;assumption.
Qed.

Lemma andb_true_eq :
  forall a b:bool, true = andb a b -> true = a /\ true = b.
Proof.
unfold andb.
intros a b;destruct a;destruct b;intros;split;try(reflexivity);try(assumption).
Defined.

Lemma andb_false_intro1 : forall b1 b2:bool, b1 = false ->andb b1  b2 = false.
Proof.
unfold andb.
intros a b;destruct a;destruct b;intros;try(reflexivity);assumption.
Qed.

Lemma andb_false_intro2 : forall b1 b2:bool, b2 = false -> andb b1 b2 = false.
Proof.
unfold andb.
intros a b;destruct a;destruct b;intros;try(reflexivity);try(assumption).
Qed.

Lemma andb_false_r : forall b:bool, andb b false = false.
Proof.
intro b;destruct b;reflexivity.
Qed.

Lemma andb_false_l : forall b:bool, andb false b = false.
Proof.
intro b. simpl. reflexivity.
Qed.

Lemma andb_diag : forall b, andb b b = b.
Proof.
intro b;destruct b;reflexivity.
Qed.

Lemma andb_true_r : forall b:bool, andb b true = b.
Proof.
intro b;destruct b;reflexivity.
Qed.

Lemma andb_true_l : forall b:bool, andb true b = b.
Proof.
simpl. reflexivity.
Qed.

Lemma andb_false_elim :
  forall b1 b2:bool, andb b1 b2 = false -> {b1 = false} + {b2 = false}.
Proof.
unfold andb.
intros a b;destruct a;destruct b;intros;try(discriminate);try(left;reflexivity).
right;reflexivity.
Defined.


Lemma andb_negb_r : forall b:bool, andb b (negb b) = false.
Proof.
intro b;destruct b;reflexivity.
Qed.

Lemma andb_comm : forall b1 b2:bool, andb b1 b2 = andb b2 b1.
Proof.
intros a b;destruct a;destruct b;reflexivity.
Qed.


Lemma andb_assoc : forall b1 b2 b3:bool, andb b1 (andb b2 b3) = andb (andb b1 b2) b3.
Proof.
intros a b c;destruct a;destruct b;destruct c;reflexivity.
Qed.

(*******************************************)
(** * Properties mixing [andb] and [orb] *)
(*******************************************)

(** Distributivity *)

Lemma andb_orb_distrib_r :
  forall b1 b2 b3:bool, andb b1 (orb b2 b3) = orb (andb b1 b2) (andb b1 b3).
Proof.
intros a b c;destruct a;destruct b;destruct c;reflexivity.
Qed.

Lemma andb_orb_distrib_l :
 forall b1 b2 b3:bool, andb (orb b1 b2) b3 = orb (andb b1 b3) (andb b2 b3).
Proof.
intros a b c;destruct a;destruct b;destruct c;reflexivity.
Qed.

Lemma orb_andb_distrib_r :
  forall b1 b2 b3:bool, orb b1 (andb b2 b3) = andb (orb b1 b2) (orb b1 b3).
Proof.
intros a b c;destruct a;destruct b;destruct c;reflexivity.
Qed.

Lemma orb_andb_distrib_l :
  forall b1 b2 b3:bool, orb (andb b1 b2) b3 = andb (orb b1 b3) (orb b2 b3).
Proof.
intros a b c;destruct a;destruct b;destruct c;reflexivity.
Qed.

Lemma absorption_andb : forall b1 b2:bool, andb b1 (orb b1 b2) = b1.
Proof.
intros a b;destruct a;destruct b;reflexivity.
Qed.

Lemma absorption_orb : forall b1 b2:bool, orb b1 (andb b1 b2) = b1.
Proof.
intros a b;destruct a;destruct b;reflexivity.
Qed.

Lemma xorb_false_r : forall b:bool, xorb b false = b.
Proof.
intros a;destruct a;reflexivity.
Qed.

Lemma xorb_false_l : forall b:bool, xorb false b = b.
Proof.
intros a;destruct a;reflexivity.
Qed.

Lemma xorb_true_r : forall b:bool, xorb b true = negb b.
Proof.
intros a;destruct a;reflexivity.
Qed.

Lemma xorb_true_l : forall b:bool, xorb true b = negb b.
Proof.
intros a;destruct a;reflexivity.
Qed.

Lemma xorb_nilpotent : forall b:bool, xorb b b = false.
Proof.
intros a;destruct a;reflexivity.
Qed.

(** Commutativity *)

Lemma xorb_comm : forall b b':bool, xorb b b' = xorb b' b.
Proof.
intros a b;destruct a;destruct b;reflexivity.
Qed.


Lemma xorb_assoc_reverse :
  forall b b' b'':bool, xorb (xorb b b') b'' = xorb b (xorb b' b'').
Proof.
intros a b c;destruct a;destruct b;destruct c;reflexivity.
Qed.

Lemma xorb_eq : forall b b':bool, xorb b b' = false -> b = b'.
Proof.
intros a b;destruct a;destruct b;simpl;intros;try(reflexivity);try(assumption).
symmetry;assumption.
Qed.

Lemma xorb_move_l_r_1 :
  forall b b' b'':bool, xorb b b' = b'' -> b' = xorb b b''.
Proof.
intros a b c.
destruct a;destruct b;destruct c;simpl;intros;try(reflexivity);try(assumption);symmetry;assumption.
Qed.

Lemma xorb_move_l_r_2 :
  forall b b' b'':bool, xorb b b' = b'' -> b = xorb b'' b'.
Proof.
intros a b c;destruct a;destruct b;destruct c;simpl;intros;
try(reflexivity);try(assumption);symmetry;assumption.
Qed.

Lemma xorb_move_r_l_1 :
  forall b b' b'':bool, b = xorb b' b'' -> xorb b' b = b''.
Proof.
intros a b c;destruct a;destruct b;destruct c;simpl;intros;
try(reflexivity);try(assumption);symmetry;assumption.
Qed.

Lemma xorb_move_r_l_2 :
  forall b b' b'':bool, b = xorb b' b'' -> xorb b b'' = b'.
Proof.
intros a b c;destruct a;destruct b;destruct c;simpl;intros;
try(reflexivity);try(assumption);symmetry;assumption.
Qed.

Lemma negb_xorb_l : forall b b', negb (xorb b b') = xorb (negb b) b'.
Proof.
intros a b;destruct a;destruct b;simpl;reflexivity.
Qed.

Lemma negb_xorb_r : forall b b', negb (xorb b b') = xorb b (negb b').
Proof.
intros a b;destruct a;destruct b;simpl;reflexivity.
Qed.

Lemma xorb_negb_negb : forall b b', xorb (negb b) (negb b') = xorb b b'.
Proof.
intros a b;destruct a;destruct b;reflexivity.
Qed.

Lemma eq_iff_eq_true : forall b1 b2, b1 = b2 <-> (b1 = true <-> b2 = true).
Proof.
intros a b;destruct a;destruct b;split;try(split);intros;
try(reflexivity);try(discriminate).
inversion H. symmetry. apply H0. reflexivity.
inversion H. apply H1. reflexivity.
Qed.

Lemma eq_true_iff_eq : forall b1 b2, (b1 = true <-> b2 = true) -> b1 = b2.
Proof.
intros a b h.
inversion h as [l r].
destruct a;destruct b;try(reflexivity).
symmetry;apply l;reflexivity.
apply r;reflexivity.
Qed.

Lemma eq_true_negb_classical : forall b:bool, negb b <> true -> b = true.
Proof.
intros b hn.
destruct b;try(reflexivity).
simpl in hn. contradiction.
Qed.

Lemma eq_true_not_negb : forall b:bool, b <> true -> negb b = true.
Proof.
intros b h.
destruct b;simpl;try(reflexivity).
contradiction.
Qed.

Lemma absurd_eq_bool : forall b b':bool, False -> b = b'.
Proof.
intros a b.
intro h.
contradiction.
Qed.

Lemma absurd_eq_true : forall b, False -> b = true.
Proof.
intros b F.
contradiction.
Qed.

Lemma trans_eq_bool : forall x y z:bool, x = y -> y = z -> x = z.
Proof.
intros x y z.
intros eqxy eqyz.
subst z. subst x. reflexivity.
Qed.

Lemma Is_true_eq_true : forall x:bool, Is_true x -> x = true.
Proof.
intros b h.
unfold Is_true in h.
destruct b;try(reflexivity).
contradiction.
Qed.

Lemma Is_true_eq_left : forall x:bool, x = true -> Is_true x.
Proof.
unfold Is_true.
intros b h.
subst b.
apply I.
Qed.

Lemma Is_true_eq_right : forall x:bool, true = x -> Is_true x.
Proof.
unfold Is_true.
intros b heq.
subst b.
apply I.
Qed.

Lemma eqb_refl : forall x:bool, Is_true (eqb x x).
Proof.
unfold Is_true.
intro b.
destruct b;simpl;apply I.
Qed.

Lemma eqb_eq : forall x y:bool, Is_true (eqb x y) -> x = y.
Proof.
intros a b.
unfold Is_true.
destruct a;destruct b;simpl;intros;try(reflexivity);contradiction.
Qed.

Lemma orb_prop_elim :
  forall a b:bool, Is_true (orb a b) -> Is_true a \/ Is_true b.
Proof.
intros a b;destruct a;destruct b;simpl;intros.
left;apply I.
left;apply I.
right;apply I.
right;contradiction.
Qed.

Lemma orb_prop_intro :
  forall a b:bool, Is_true a \/ Is_true b -> Is_true (orb a b).
Proof.
intros a b;destruct a;destruct b;simpl;intros;try(apply I).
inversion H;contradiction.
Qed.

Lemma andb_prop_intro :
  forall b1 b2:bool, Is_true b1 /\ Is_true b2 -> Is_true (andb b1 b2).
Proof.
intros a b;destruct a;destruct b;simpl;intros h;inversion h as [l r].
apply I.
contradiction.
contradiction.
contradiction.
Qed.

Lemma andb_prop_elim :
  forall a b:bool, Is_true (andb a b) -> Is_true a /\ Is_true b.
Proof.
intros a b;destruct a;destruct b;simpl;intros;split;
try(apply I);try(contradiction).
Qed.

Lemma eq_bool_prop_intro :
  forall b1 b2, (Is_true b1 <-> Is_true b2) -> b1 = b2.
Proof.
intros a b;destruct a;destruct b;simpl;intro h;inversion h as [l r];try(reflexivity).
contradiction.
contradiction.
Qed.

Lemma eq_bool_prop_elim : forall b1 b2, b1 = b2 -> (Is_true b1 <-> Is_true b2).
Proof.
intros a b;destruct a;destruct b;simpl;split;intro h;
try(apply I);try(discriminate);try(contradiction).
Qed.

Lemma negb_prop_elim : forall b, Is_true (negb b) -> ~ Is_true b.
Proof.
intros b;destruct b;simpl;intros h n;contradiction.
Qed.

Lemma negb_prop_intro : forall b, ~ Is_true b -> Is_true (negb b).
Proof.
intro b;destruct b;simpl;intro h.
contradiction. trivial.
Qed.

Lemma negb_prop_classical : forall b, ~ Is_true (negb b) -> Is_true b.
Proof.
intros b;destruct b;simpl;intro h.
trivial.
apply h;trivial.
Qed.

Lemma negb_prop_involutive : forall b, Is_true b -> ~ Is_true (negb b).
Proof.
intro b;destruct b;simpl;intros h n;contradiction.
Qed.

Lemma andb_if : forall (A:Type)(a a':A)(b b' : bool),
  (if (andb b b') then a else a') =
  (if b then if b' then a else a' else a').
Proof.
intros A a1 a2 b1 b2.
destruct b1;destruct b2;simpl;reflexivity.
Qed.

Lemma negb_if : forall (A:Type)(a a':A)(b:bool),
 (if negb b then a else a') =
 (if b then a' else a).
Proof.
intros A x y b;destruct b;simpl;reflexivity.
Qed.

Definition andbl (a b:bool) := if a then b else false.
Definition orbl (a b:bool) := (if a then true else b).

Lemma andb_lazy_alt : forall a b : bool, andb a b = andbl a b.
Proof.
intros a b;destruct a;destruct b;reflexivity.
Qed.

Lemma orb_lazy_alt : forall a b : bool, orb a b = orbl a b.
Proof.
intros a b;destruct a;destruct b;reflexivity.
Qed.

Inductive reflect (P : Prop) : bool -> Set :=
  | ReflectT : P -> reflect P true
  | ReflectF : ~ P -> reflect P false.

Lemma reflect_iff : forall P b, reflect P b -> (P<->b=true).
Proof.
intros P b h.
destruct b;split;simpl;intro p;try(reflexivity);inversion h;try(assumption);try(reflexivity);try(contradiction);try(discriminate).
Qed.

Lemma iff_reflect : forall P b, (P<->b=true) -> reflect P b.
Proof.
intros P b.
destruct b;simpl;intro h;inversion h as [l r].
apply ReflectT. apply r. reflexivity.
apply ReflectF. intro p.
discriminate (l p).
Defined.

Lemma reflect_dec : forall P b, reflect P b -> {P}+{~P}.
Proof.
intros P b h.
destruct b;inversion h.
left;assumption.
right;assumption.
Defined.