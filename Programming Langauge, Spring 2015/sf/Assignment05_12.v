Require Export Assignment05_11.

(* problem #12: 10 points *)




(** 2 stars (false_beq_nat)  *)

Lemma false_beq_nat_sub0 : forall n m: nat,
  beq_nat n m = true -> n = m.
Proof.
  induction n.
  simpl.
  intros.
  destruct m.
  reflexivity.
  inversion H.
  simpl.
  intros.
  destruct m.
  inversion H.
  apply IHn in H.
  rewrite H.
  reflexivity.
Qed.

Theorem false_beq_nat : forall n m : nat,
     n <> m ->
     beq_nat n m = false.
Proof.
  unfold not.
  intros.
  destruct (beq_nat n m) eqn:h0.
  apply false_beq_nat_sub0 in h0.
  apply H in h0.
  inversion h0.
  reflexivity.
Qed.
(** [] *)




