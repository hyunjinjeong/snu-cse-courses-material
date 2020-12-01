Require Export Assignment08_10.

(* problem #11: 10 points *)

(** **** Exercise: 2 stars (assign_aequiv)  *)

Lemma up_same: forall x1 k1 k2 (f : state),
  f k1 = x1 ->
  (update f k1 x1) k2 = f k2.
Proof.
  intros.
  unfold update.
  destruct (eq_id_dec k1 k2).
  subst.
  reflexivity.
  reflexivity.
Qed.

Theorem assign_aequiv : forall X e,
  aequiv (AId X) e -> 
  cequiv SKIP (X ::= e).
Proof.
  intros.
  split; intros; inversion H0; subst.
  assert (st' = update st' X (aeval st' e)).
  apply functional_extensionality.
  intros.
  rewrite up_same.
  reflexivity.
  apply H.
  rewrite H1 at 2.
  apply E_Ass.
  reflexivity.
  assert (st = update st X (aeval st e)).
  apply functional_extensionality.
  intros.
  rewrite up_same.
  reflexivity.
  apply H.
  rewrite <- H1.
  constructor.
Qed.


(*-- Check --*)
Check assign_aequiv : forall X e,
  aequiv (AId X) e -> 
  cequiv SKIP (X ::= e).

