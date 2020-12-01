Require Export Assignment05_35.

(* problem #36: 10 points *)

Theorem ble_nat_true : forall n m,
  ble_nat n m = true -> n <= m.
Proof. 
  intros n.
  induction n.
  intros.
  apply O_le_n.
  intros.
  destruct m.
  inversion H.
  inversion H.
  apply n_le_m__Sn_le_Sm.
  apply IHn.
  apply H1.
Qed.

