Inductive answer : Type :=
| yes : answer
| no : answer 
| unknown : nat -> answer.

Definition toggle_answer (a:answer) : answer := match a with
| yes => no
| no => yes
| unknown n => unknown n
end.
Compute (toggle_answer yes).

Example test_yes_no: (toggle_answer yes) = no.
Proof.
simpl.
reflexivity.
Qed.

Inductive answer_bool : Type :=
  | ab_answer : answer -> answer_bool
  | ab_bool : bool -> answer_bool.

Definition answer_bool_positive (x : answer_bool) : bool :=
  match x with
  | ab_answer yes => true
  | ab_answer _ => false
  | ab_bool true => true
  | ab_bool _ => false
  end.

Example answer_bool_positive_true_true: (answer_bool_positive (ab_bool true)) = true.
Proof.
simpl.
reflexivity.
Qed.

Definition previous (n : nat) : nat :=
match n  with
| O => O
| S p => p
end.

Example previous_2_1: (previous 2) = 1.
Proof.
simpl.
reflexivity.
Qed.

Fixpoint evenb (n:nat) : bool :=
match n with
| 0 => true
| S 0 => false
| S (S p) => evenb p
end.

Fixpoint minus (n m : nat) : nat :=
match n, m with
| O , _ => O
| S _ , O => n
| S n', S m' => minus n' m'
end.

Definition foo (a:answer) : answer.
Admitted.

Theorem thm  : forall n m:answer, n=m -> foo n = foo m.
intros n m.
intro eq.
rewrite -> eq.
reflexivity.

Theorem plus_O_n : forall n : nat, 0 + n = n.
Proof.
  intros n. simpl. reflexivity. Qed.

Theorem mult_0_plus : forall n m : nat,
  (0 + n) * m = n * m.
Proof.
  intros n m.
  rewrite <- plus_O_n.
  reflexivity. Qed.

Theorem answer2 : forall a:answer, toggle_answer (toggle_answer a)=a.
intro a.
destruct a.
simpl. reflexivity.
simpl. reflexivity.
simpl. reflexivity.
Qed.

Theorem x : forall n:nat, n=n.
intro n.
destruct (plus n 1) eqn:Y.
reflexivity.