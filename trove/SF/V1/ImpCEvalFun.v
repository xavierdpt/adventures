Require Import Coq.omega.Omega.
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
intros com src dst.
intro he.
inversion_clear he as [t h].
generalize dependent dst.
generalize dependent src.
generalize dependent com.
induction t as [|t hi].
  intros com src dst h.
  simpl in h. inversion h.
intros com src dst h.
simpl in h.
destruct com.
  inversion h as [heq].
  subst dst.
  apply E_Skip.
  inversion h as [heq].
  Search CAss.
  apply E_Ass.
  reflexivity.
  destruct (ceval_step src com1 t) as [tmp|] eqn:heq.
    simpl in h.
    apply (E_Seq com1 com2 src tmp dst).
     apply hi. assumption. 
     apply hi. assumption.
simpl in h. inversion h. 
  destruct (beval src b) eqn:heq.
    Search CIf.
    apply E_IfTrue. assumption.
    apply hi. assumption.
    apply E_IfFalse. assumption. apply hi. assumption.
  destruct (beval src b) eqn:heq.
    destruct (ceval_step src com t) eqn:heqq.
    simpl in h.
    apply (E_WhileTrue src s dst). assumption. apply hi. rewrite heqq. reflexivity.
    apply hi. rewrite h. reflexivity.
simpl in h. inversion h.
   inversion h. subst dst. apply E_WhileFalse. assumption.
Qed.

Theorem ceval_step_more : forall n m src dst com,
n <= m ->
ceval_step src com n = Some dst ->
ceval_step src com m = Some dst.
(* This theorems stays that whenever a computation bounded to n steps terminates on some state 'dst',
then performing the same computation with a larger bound produces the same state 'dst'. *)
intro n.
(* We proceed by induction on n *)
induction n as [|n HI].
(* This yields two case : the basis case and the general case *)
{ (* Basis case : a 0 bound never produces a state, therefore the other hypothesis is inconsistent *)
  simpl. intros m src dst c hle impossible.
  inversion impossible.
}
{ (* General case *)
  intros m src dst com hle.
  (* we destruct m to discard the case m=0 which is impossible*)
  destruct m as [|m].
  { (* m=0 makes the hypothesis inconsistents *)
    inversion hle.
  }
  { (* now we can invert hle to distinguish equality and strict inequality *)
    inversion hle as [heq|y hley heqy].
    { (* equality : when bounds are identical, the hypothesis is the same as the goal *)
      subst m. intro h. assumption.
    }
    { (* strict inequality *)
      subst y.
      apply le_S_n in hle.
      simpl.
      (* Here, we need to consider every command individually *)
      destruct com as [|var exp|com1 com2| exp com1 com2  | exp com1] eqn:heqcom.
      { (* Skip : by definition of skip, the next state is the same as the previous state *)
        intro eq. apply eq.
      }
      { (* Assignment : here, the next state is defined direclty from the previous state in the definition of assignment *)
        intro eqdef. apply eqdef.
      }
      { (* Sequences *)
        intro letopt.
        destruct (ceval_step src com1 n) as [tmp|] eqn:eqopt.
        { (* Case where com1 evaluates to something (tmp) *)
          (* We first simplify letopt *) simpl in letopt.
          (* We apply the induction step on com1 in eqopt *) apply (HI m) in eqopt.
          { (* We can now substitute the evaluation of com1 with its result *)
            rewrite eqopt.
            (* This allows simplifying *)
            simpl.
            (* Then we apply the induction step for com2 *)
            apply HI.
            { (* n <=m *) assumption. }
            { (* The fact that tmp and com2 yields dst is in the assumptions *) assumption. }
         }
         { (* The first induction step also requires n<=m which is in the assumption *) assumption. }
        }
        { (* Case where com1 evaluates to nothing => absurd *)
          simpl in letopt. inversion letopt.
        }
      }
      { (* Conditionals : we distinguish true and false *)
        destruct (beval src exp) as [] eqn:heqb.
        (* In both case, the behaviour is part of the assumption after simplification. *)
        { intro hstep.
          (* rewrite m into n *) apply HI.
          { (* n<=m *) assumption. }
          { (* result *) assumption. }
        }
        { (* same *) intro hstep. apply HI. { assumption. } { assumption. } }
      }
      { (* While *)
        destruct (beval src exp) eqn:heqb.
        { (* true *)
          destruct (ceval_step src com1 n) as [tmp|] eqn:heqopt.
          { (* Here, we proceed like in sequences *)
            simpl.
            intro ceval_tmp.
            apply (HI m) in heqopt. 
            { rewrite heqopt. simpl. apply HI.
              { (* n<=m *) assumption. }
              { (* result *) assumption. }
            }
            { (* n<=l *) assumption. }
          }
          {
            simpl. intro impossible. inversion impossible.
          }
        }
        { (* false : immediate*)
          intro eq. apply eq.
        }
      }
    }
  }
}
Qed.

Theorem ceval_deterministic' : forall c st st1 st2, (ceval c st st1) -> (ceval c st st2) -> st1 = st2.
Admitted.
