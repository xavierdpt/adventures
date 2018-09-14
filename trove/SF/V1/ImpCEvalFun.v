Require Import Imp Maps.

Definition LetOpt (e1 : option state) (e2 : state -> option state) := 
match e1 with
   | Some x => e2 x
   | None => None
 end.


Fixpoint ceval_step (st : state) (c : com) (i : nat)
                    : option state :=
  match i with
  | O => None
  | S i' =>
    match c with
      | CSkip =>
          Some st
      | CAss l a1 =>
          Some (t_update st l (aeval st a1))
      | CSeq c1 c2 => (LetOpt (ceval_step st c1 i') (fun st'=>ceval_step st' c2 i'))
      | CIf b c1 c2 =>
          if (beval st b)
            then ceval_step st c1 i'
            else ceval_step st c2 i'
      | CWhile b1 c1 =>
          if (beval st b1)
          then (LetOpt (ceval_step st c1 i') (fun st' =>  ceval_step st' c i'))
          else Some st
    end
  end.

Theorem ceval_step__ceval: forall c st st',
      (exists i, ceval_step st c i = Some st') ->
      (ceval c st st').
Admitted.

Theorem ceval_step_more : forall i1 i2 st st' c, i1 <= i2 -> ceval_step st c i1 = Some st' -> ceval_step st c i2 = Some st'.
Admitted.

Theorem ceval_deterministic' : forall c st st1 st2, (ceval c st st1) -> (ceval c st st2) -> st1 = st2.
Admitted.
