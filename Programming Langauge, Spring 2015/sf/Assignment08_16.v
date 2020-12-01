Require Export Assignment08_15.

(* problem #16: 10 points *)

Lemma optimize_0plus_aexp_sound:
  atrans_sound optimize_0plus_aexp.
Proof.
  intros a st.
  aexp_cases (induction a) Case; simpl;
  try reflexivity; try (rewrite IHa1; rewrite IHa2; reflexivity).
  destruct a1; try destruct n; destruct a2; try destruct n;
  try rewrite IHa2; try destruct n0; try simpl in *; try omega.
Qed.

(*-- Check --*)
Check optimize_0plus_aexp_sound:
  atrans_sound optimize_0plus_aexp.

