Require Export Assignment05_17.

(* problem #18: 10 points *)





(** 1 star (gorgeous_plus13)  *)
Theorem gorgeous_plus13: forall n, 
  gorgeous n -> gorgeous (13+n).
Proof.
  intros.
  induction H.
  simpl.
  apply g_plus5.
  apply g_plus5.
  apply g_plus3.
  apply g_0.
  simpl.
  apply g_plus5.
  apply g_plus5.
  apply g_plus3.
  apply g_plus3.
  apply H.
  simpl.
  apply g_plus5.
  apply IHgorgeous.
Qed.
(** [] *)




