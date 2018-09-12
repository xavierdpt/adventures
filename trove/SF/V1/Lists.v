Require Export Induction.

Inductive natprod : Type :=
| pair : nat -> nat -> natprod.

Definition fst (p:natprod) := match p with
| pair x y => x
end.

Definition snd (p:natprod) := match p with
| pair x y => y
end.

Theorem surjective_pairing_n_m : forall n m : nat, pair n m = pair (fst (pair n m)) (snd (pair n m)).
reflexivity.
Show Proof.
Qed.

Theorem surjective_pairing : forall p : natprod, p = pair (fst p) (snd p).
destruct p.
reflexivity.
Show Proof.
Qed.

Inductive natlist : Type :=
| nil : natlist
| cons : nat->natlist->natlist
.

Fixpoint repeat (n count : nat) : natlist :=
match count with
| O => nil
| S c' => cons n (repeat n c')
end.

Fixpoint length (l : natlist) : nat :=
match l with
| nil => O
| cons n rest => S (length rest)
end.

Fixpoint append (l1 l2 : natlist) : natlist := match l1 with
| nil => l2
| cons n1 rest1 => cons n1 (append rest1 l2)
end.

Definition head (l:natlist) (d:nat) : nat := match l with
| nil => d
| cons n _ => n
end.

Definition tail (l:natlist) : natlist := match l with
| nil => nil
| cons _ t => t
end.

Theorem nil_app : forall l:natlist, (append nil l) = l.
reflexivity.
Qed.

Theorem tl_length_pred : forall l:natlist, pred (length l) = length (tail l).
destruct l;reflexivity.
Show Proof.
Qed.

Theorem append_associative : forall (l m n : natlist), (append (append l m) n) = (append l (append m n)).
induction l.
reflexivity.
simpl.
intros m n0.
rewrite (IHl m n0).
reflexivity.
Show Proof.
Qed.

Fixpoint rev (l:natlist) : natlist :=
match l with
| nil => nil
| cons n rest => (append rest (cons n nil))
end.

Theorem app_length : forall l1 l2 : natlist, length (append l1 l2) = (plus (length l1) (length l2)).
intro l.
induction l.
reflexivity.
simpl.
intro l2.
rewrite(IHl l2).
reflexivity.
Qed.

Theorem rev_length : forall l : natlist, length (rev l) = length l.
induction l.
reflexivity.
simpl.
rewrite -> app_length.
rewrite -> plus_commute.
reflexivity.
Qed.

Inductive natoption : Type :=
| Some : nat -> natoption
| None : natoption
.

Fixpoint nth (l:natlist) (n:nat) : natoption := match l with
| nil => None
| cons e rest => if beq_nat n O then Some e else nth rest (pred n)
end.

Definition elim (o:natoption) (d:nat) := match o with
| None => d
| Some n => n
end.

Inductive id : Type :=
| Id : nat -> id.

Definition beq_id (i j : id) :=
match i, j with
| Id ni, Id nj => beq_nat ni nj
end.

Inductive partial_map : Type :=
| empty : partial_map
| record : id -> nat -> partial_map -> partial_map.

Definition update (d:partial_map) (x:id) (value:nat) : partial_map := record x value d.

Fixpoint find (x:id) (d:partial_map) : natoption := match d with 
| empty => None
| record y v d' => if beq_id x y then Some v else find x d'
end.



