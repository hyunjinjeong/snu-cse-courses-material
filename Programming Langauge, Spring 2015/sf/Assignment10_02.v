Require Export Assignment10_01.

(* problem #02: 10 points *)

(** As a sanity check on this change, let's re-verify determinism 

    Proof sketch: We must show that if [x] steps to both [y1] and [y2]
    then [y1] and [y2] are equal.  Consider the final rules used in
    the derivations of [step x y1] and [step x y2].

    - If both are [ST_PlusConstConst], the result is immediate.

    - It cannot happen that one is [ST_PlusConstConst] and the other
      is [ST_Plus1] or [ST_Plus2], since this would imply that [x] has
      the form [P t1 t2] where both [t1] and [t2] are
      constants (by [ST_PlusConstConst]) AND one of [t1] or [t2] has
      the form [P ...].

    - Similarly, it cannot happen that one is [ST_Plus1] and the other
      is [ST_Plus2], since this would imply that [x] has the form
      [P t1 t2] where [t1] both has the form [P t1 t2] and
      is a value (hence has the form [C n]).

    - The cases when both derivations end with [ST_Plus1] or
      [ST_Plus2] follow by the induction hypothesis. [] *)

(** Most of this proof is the same as the one above.  But to get
    maximum benefit from the exercise you should try to write it from
    scratch and just use the earlier one if you get stuck. *)

Theorem step_deterministic_alt: deterministic step.
Proof.
  unfold deterministic.
  intros.
  generalize dependent y2.
  induction H.
  intros.
  destruct y2.
  inversion H0.
  reflexivity.
  inversion H0.
  subst.
  inversion H1.
  subst.
  inversion H5.
  intros.
  destruct y2.
  inversion H0.
  subst.
  inversion H.
  inversion H0.
  subst.
  apply IHstep in H2.
  rewrite H2.
  reflexivity.
  subst.
  inversion H4.
  rewrite <- H1 in H.
  inversion H.
  intros.
  destruct y2.
  inversion H1.
  subst.
  inversion H0.
  inversion H.
  subst.
  inversion H1.
  subst.
  inversion H3.
  subst.
  apply IHstep in H7.
  rewrite H7.
  reflexivity.
Qed.

(*-- Check --*)
Check step_deterministic_alt: deterministic step.

