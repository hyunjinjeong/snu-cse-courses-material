Require Export Assignment08_07.

(* problem #08: 10 points *)

(** **** Exercise: 3 stars (swap_if_branches)  *)
(** Show that we can swap the branches of an IF by negating its
    condition *)

Theorem swap_if_branches: forall b e1 e2,
  cequiv
    (IFB b THEN e1 ELSE e2 FI)
    (IFB BNot b THEN e2 ELSE e1 FI).
Proof.
  unfold cequiv.
  intros.
  split.
  intros.
  inversion H.
  subst.
  apply E_IfFalse.
  simpl.
  rewrite H5.
  reflexivity.
  apply H6.
  subst.
  apply E_IfTrue.
  simpl.
  rewrite H5.
  reflexivity.
  apply H6.
  intros.
  inversion H.
  subst.
  apply E_IfFalse.
  simpl in H5.
  assert (forall (bo: bool), negb bo = true -> bo = false).
  intros.
  destruct bo.
  inversion H0.
  reflexivity.
  apply H0 in H5.
  apply H5.
  apply H6.
  subst.
  apply E_IfTrue.
  simpl in H5.
  assert (forall (bo: bool), negb bo = false -> bo = true).
  intros.
  destruct bo.
  inversion H0.
  reflexivity.
  inversion H0.
  apply H0 in H5.
  apply H5.
  apply H6.
Qed.


(*-- Check --*)
Check swap_if_branches: forall b e1 e2,
  cequiv
    (IFB b THEN e1 ELSE e2 FI)
    (IFB BNot b THEN e2 ELSE e1 FI).

