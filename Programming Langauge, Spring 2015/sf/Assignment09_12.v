Require Export Assignment09_11.

(* problem #12: 10 points *)

(** **** Exercise: 2 stars, advanced (hoare_asgn_weakest)  *)
(** Show that the precondition in the rule [hoare_asgn] is in fact the
    weakest precondition. *)

Theorem hoare_asgn_weakest : forall Q X a,
  is_wp (Q [X |-> a]) (X ::= a) Q.
Proof.
  unfold is_wp.
  unfold assert_implies.
  unfold hoare_triple.
  unfold assn_sub.
  intros.
  split.
  intros.
  inversion H.
  subst.
  apply H0.
  intros.
  apply H with (st := st).
  apply E_Ass.
  reflexivity.
  apply H0.
Qed.

(*-- Check --*)
Check hoare_asgn_weakest : forall Q X a,
  is_wp (Q [X |-> a]) (X ::= a) Q.
