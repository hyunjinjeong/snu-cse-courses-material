Require Export Assignment05_36.

(* problem #37: 10 points *)

  

Theorem le_ble_nat : forall n m,
  n <= m ->
  ble_nat n m = true.
Proof.
  intros.
  generalize dependent n.
  induction m.
  intros.
  inversion H.
  reflexivity.
  intros.
  destruct n.
  reflexivity.
  apply Sn_le_Sm__n_le_m in H.
  apply IHm.
  apply H.
Qed.

