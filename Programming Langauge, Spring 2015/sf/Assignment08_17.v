Require Export Assignment08_16.

(* problem #17: 10 points *)

Lemma optimize_0plus_bexp_sound:
  btrans_sound optimize_0plus_bexp.
Proof.
  intros b st.
  induction b; try simpl in *; try reflexivity.
  rewrite <- 2 optimize_0plus_aexp_sound. reflexivity.
  rewrite <- 2 optimize_0plus_aexp_sound. reflexivity.
  rewrite IHb. reflexivity.
  rewrite IHb1. rewrite IHb2. reflexivity.
Qed.

(*-- Check --*)
Check optimize_0plus_bexp_sound:
  btrans_sound optimize_0plus_bexp.

