Require Export Assignment07_04.

(* problem #05: 10 points *)

(** **** Exercise: 1 star (update_eq)  *)



Theorem update_eq : forall n x st,
  (update st x n) x = n.
Proof.
  unfold update.
  intros.
  destruct (eq_id_dec x x) eqn:h0.
  reflexivity.
  unfold not in n0.
  apply ex_falso_quodlibet.
  apply n0.
  reflexivity.
Qed.
(** [] *)

