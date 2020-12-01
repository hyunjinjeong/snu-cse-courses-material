Require Export Assignment10_08.

(* problem #09: 10 points *)

(** **** Exercise: 3 stars (step__eval)  *)
Lemma step__eval : forall t t' n,
     t ==> t' ->
     t' || n ->
     t || n.
Proof.
  intros t t' n Hs. generalize dependent n.
  induction Hs.
  intros.
  inversion H.
  subst.
  apply E_Plus.
  constructor.
  constructor.
  intros.
  inversion H.
  subst.
  apply E_Plus.
  apply IHHs.
  apply H2.
  apply H4.
  intros.
  inversion H.
  subst.
  inversion H0.
  subst.
  apply E_Plus.
  apply H3.
  apply IHHs.
  apply H5.
Qed.

(*-- Check --*)
Check step__eval : forall t t' n,
     t ==> t' ->
     t' || n ->
     t || n.

