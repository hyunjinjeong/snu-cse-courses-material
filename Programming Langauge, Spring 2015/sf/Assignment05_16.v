Require Export Assignment05_15.

(* problem #16: 10 points *)




Lemma b_times2_sub0: forall n,
  n = n + 0.
Proof.
  intros.
  induction n.
  simpl.
  reflexivity.
  simpl.
  rewrite <- IHn.
  reflexivity.
Qed.

(** 2 stars (b_times2)  *)
Theorem b_times2: forall n, beautiful n -> beautiful (2*n).
Proof.
  intros.
  induction H.
  simpl.
  apply b_0.
  simpl.
  apply b_sum with (n:=3) (m:=3).
  apply b_3.
  apply b_3.
  simpl.
  apply b_sum with (n:=5) (m:=5).
  apply b_5.
  apply b_5.
  simpl.
  replace (n + m + 0) with (n + m).
  apply b_sum with (n:= n+m) (m:= n+m).
  apply b_sum.
  apply H.
  apply H0.
  apply b_sum.
  apply H.
  apply H0.
  apply b_times2_sub0.
Qed.
(** [] *)



