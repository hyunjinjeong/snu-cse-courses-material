Require Export Assignment08_11.

(* problem #12: 10 points *)

(** **** Exercise: 3 stars, optional (CSeq_congruence)  *)
Theorem CSeq_congruence : forall c1 c1' c2 c2',
  cequiv c1 c1' -> cequiv c2 c2' ->
  cequiv (c1;;c2) (c1';;c2').
Proof. 
  unfold cequiv.
  intros.
  split.
  intros.
  inversion H1.
  subst.
  apply E_Seq with (st' := st'0).
  apply H in H4.
  apply H0 in H7.
  apply H4.
  apply H0 in H7.
  apply H7.
  intros.
  inversion H1.
  subst.
  apply E_Seq with (st' := st'0).
  apply H in H4.
  apply H4.
  apply H0 in H7.
  apply H7.
Qed.

(*-- Check --*)
Check CSeq_congruence : forall c1 c1' c2 c2',
  cequiv c1 c1' -> cequiv c2 c2' ->
  cequiv (c1;;c2) (c1';;c2').

