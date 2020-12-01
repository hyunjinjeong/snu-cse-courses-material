Require Export Assignment12_03.

(* problem #04: 10 points *)

Corollary soundness : forall t t' T,
  empty |- t \in T -> 
  t ==>* t' ->
  ~(stuck t').
Proof.
  unfold not. unfold stuck. unfold normal_form. unfold not.
  intros.
  destruct H1.
  assert (\empty |- t \in T).
  apply H.
  induction H0; subst.
  apply progress in H. inversion H. apply H2 in H0. apply H0.
  apply H1 in H0. apply H0.
  apply preservation with (t' := y) in H3.
  apply IHmulti.
  apply H3. apply H1. apply H2. apply H3.
  apply H0.
Qed.

(*-- Check --*)
Check soundness : forall t t' T,
  empty |- t \in T -> 
  t ==>* t' ->
  ~(stuck t').

