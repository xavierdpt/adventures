Require Export Lists.

Inductive list X:Type : Type :=
| nil : list X
| cons : X -> list X -> list X
.
Arguments nil {X}.
Arguments cons {X} _ _.

Fixpoint repeat {X} x count : list X :=
match count with
| O => nil
| S count' => cons x (repeat x count')
end
.

Fixpoint append {X} (l1 l2 : list X) : list X :=
match l1 with
| nil => l2
| cons h t => cons h (append t l2)
end.

Fixpoint reverse {X} (l:list X) : list X := match l with
| nil => nil
| cons h t => append (reverse t) (cons h nil)
end.

Fixpoint length {X} (l:list X) : nat := match l with
| nil => O
| cons _ tail => S (length tail)
end.

Inductive prod (X Y : Type) : Type :=
| pair : X -> Y -> prod X Y.
Arguments pair {X} {Y} _ _ .

Definition first {X Y : Type} (p:prod X Y) : X := match p with
| pair x _ => x
end.

Definition second {X Y : Type} (p:prod X Y) : Y := match p with
| pair _ y => y
end.

Fixpoint combine {X Y : Type} (lx : list X) (ly : list Y) : list (prod X Y) :=
match lx, ly with
| nil, _ => nil
| _, nil => nil
| cons headx tailx, cons heady taily => (append (cons (pair headx heady) nil) (combine tailx taily))
end.

Inductive option (X:Type) : Type :=
| Some : X -> option X
| None : option X
.
Arguments Some {X} _.
Arguments None {X}.

Fixpoint nth {X:Type} (l:list X) (n:nat) : option X :=
match l with
| nil => None
| cons head tail => if beq_nat n O then Some head else nth tail (pred n)
end.

Fixpoint filter {X:Type} (test:X->bool) (l:list X) : list X :=
match l with
| nil => nil
| cons head tail => if test head then (cons head (filter test tail)) else filter test tail
end.

Fixpoint map {X Y : Type} (f:X->Y) (l:list X) : list Y :=
match l with
| nil => nil
| cons head tail => cons (f head) (map f tail)
end.

Fixpoint fold {X Y : Type} (f:X->Y->Y) (l:list X) (b:Y) : Y :=
match l with
| nil => b
| cons head tail => f head (fold f tail b)
end.




