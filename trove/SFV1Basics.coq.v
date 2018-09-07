Inductive answer : Type :=
| yes : answer
| no : answer 
| unknown : answer.

Definition toggle_answer (a:answer) : answer := match a with
| yes => no
| no => yes
| unknown => unknown
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