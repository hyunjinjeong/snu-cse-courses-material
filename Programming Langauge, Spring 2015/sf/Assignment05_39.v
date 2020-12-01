Require Export Assignment05_38.

(* problem #39: 10 points *)

Theorem ble_nat_false : forall n m,
  ble_nat n m = false -> ~(n <= m).
Proof.
  unfold not.
  intros.
  apply le_ble_nat in H0.
  rewrite H in H0.
  inversion H0.
Qed.
(** [] *)

