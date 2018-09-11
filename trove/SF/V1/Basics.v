Inductive day : Type :=
| monday : day
| tuesday : day
| wednesday : day
| thursday : day
| friday : day
| saturday : day
| sunday : day.

Definition next_weekday (d:day) : day :=
match d with
| monday => tuesday
| tuesday => wednesday
| wednesday => thursday
| thursday => friday
| friday => monday
| saturday => monday
| sunday => monday
end.


Example test_next_weekday : (next_weekday (next_weekday saturday)) = tuesday.
reflexivity.
Show Proof.
Qed.

Example test_next_weekday2 : (next_weekday (next_weekday saturday)) = tuesday := eq_refl.

Inductive bool : Type :=
| true : bool
| false : bool.

Definition negb (b:bool) : bool :=
match b with
| true => false
| false => true
end.

Definition andb (a b:bool) : bool :=
match a with
| true => b
| false => false
end.

Definition orb (a b:bool) : bool :=
match a with
| true => true
| false => b
end.

Example test_orb1 : (orb true false) = true := eq_refl.
Example test_orb2 : (orb false false) = false := eq_refl.
Example test_orb3 : (orb false true) = true := eq_refl.
Example test_orb4 : (orb true true) = true := eq_refl.

Inductive rgb : Type :=
| red : rgb
| green : rgb
| blue : rgb.

Inductive color : Type :=
| black : color
| white : color
| primary : rgb -> color.

Definition monochrome (c:color) : bool :=
match c with
| black => true
| white => true
| primary p => false
end.

Definition isred (c:color) : bool :=
match c with
| black => false
| white => false
| primary red => true
| primary _ => false
end.

Inductive nat : Type :=
| O : nat
| S : nat -> nat.


Definition pred (n:nat) : nat :=
match n with
| O => O
| S m => m
end.

Definition minustwo (n:nat) : nat :=
match n with
| O => O
| S O => O
| S (S m) => m
end.

Fixpoint evenb (n:Datatypes.nat) : bool :=
match n with
| Datatypes.O => true
| Datatypes.S Datatypes.O => false
| Datatypes.S (Datatypes.S m) => evenb m
end.

Definition oddb (n:Datatypes.nat) : bool := negb (evenb n).

Example test_oddb1 : oddb 1 = true := eq_refl.
Example test_oddb2 : oddb 4 = false := eq_refl.

Fixpoint plus (n m:nat) : nat :=
match n with
| O => m
| S n' => S(plus n' m)
end.

Fixpoint mult (n m:nat) : nat :=
match n with
| O => O
| S n' => plus m (mult n' m)
end.

Fixpoint minus (n m:nat) : nat :=
match n, m with
| O, _ => O
| S _ , O => n
| S n', S m' => minus n' m'
end.

Fixpoint exp (base power : nat) : nat :=
match power with
| O => S O
| S p => mult base (exp base p)
end.

Fixpoint beq_nat (n m:nat) : bool :=
match n, m with
| O, O => true
| O, S m' => false
| S n', O => false
| S n', S m' => beq_nat n' m'
end.

Fixpoint leb (n m:nat) : bool :=
match n, m with
| O, O => true
| O, S m' => true
| S n', O => false
| S n', S m' => leb n' m'
end.

Theorem plus_O_n : forall n : nat, plus O n = n.
reflexivity.
Show Proof.
Qed.

Theorem plus_1_l : forall n:nat, plus (S O) n = S n.
reflexivity.
Show Proof.
Qed.

Theorem mult_0_1 : forall n : nat, mult O n = O.
reflexivity.
Show Proof.
Qed.

Theorem plus_id_example : forall n m : nat, n = m -> plus n n = plus m m.
intros n m.
intro heq.
Show Proof.
rewrite heq.
Show Proof.
reflexivity.
Show Proof.
Qed.

Definition plus_id_example' :
forall n m : nat, n = m -> plus n n = plus m m :=
fun (n m : nat) (heq : n=m) =>
@eq_ind_r nat m (fun x:nat => plus x x = plus m m) eq_refl n heq.


Theorem plus_1_neq_0 : forall n : nat, beq_nat (plus n (S O)) O = false.
intro n.
Print nat.
destruct n as [|m];reflexivity.
Show Proof.
Qed.


Theorem negb_involutive : forall b : bool, negb (negb b) = b.
destruct b;reflexivity.
Show Proof.
Qed.

Theorem andb_commutative : forall b c, andb b c = andb c b.
destruct b;destruct c;reflexivity.
Show Proof.
Qed.

Theorem andb3_exchange : forall b c d, andb (andb b c) d = andb (andb b d) c.
destruct b;destruct c;(try reflexivity);destruct d;reflexivity.
Show Proof.
Qed.





