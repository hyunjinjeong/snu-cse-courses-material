Require Export Assignment05_31.

(* problem #32: 10 points *)

Theorem Sn_le_Sm__n_le_m : forall n m,
  S n <= S m -> n <= m.
Proof.
  intros.
  inversion H.
  apply le_n.
  apply le_trans with (n := S n).
  apply le_S.
  apply le_n.
  apply H2.
Qed.