Require Export Assignment05_05.

(* problem #06: 10 points *)


(** 2 stars, optional (orb_false)  *)
Theorem orb_prop : forall b c,
  orb b c = true -> b = true \/ c = true.
Proof.
  intros.
  induction b.
  left.
  reflexivity.
  destruct c.
  right.
  reflexivity.
  left.
  inversion H.
Qed.


