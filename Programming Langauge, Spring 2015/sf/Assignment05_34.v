Require Export Assignment05_33.

(* problem #34: 10 points *)

Theorem plus_lt : forall n1 n2 m,
  n1 + n2 < m ->
  n1 < m /\ n2 < m.
Proof. 
 unfold lt.
 induction m.
 intros.
 inversion H.
 intros.
 split.
 apply Sn_le_Sm__n_le_m in H.
 apply n_le_m__Sn_le_Sm.
 apply le_trans with (n := n1 + n2).
 apply le_plus_l.
 apply H.
 apply Sn_le_Sm__n_le_m in H.
 apply n_le_m__Sn_le_Sm.
 rewrite plus_comm in H.
 apply le_trans with (n := n2 + n1).
 apply le_plus_l.
 apply H.
Qed.

