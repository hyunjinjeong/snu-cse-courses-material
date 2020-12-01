Require Export Assignment10_12.

(* problem #13: 10 points *)

(** **** Exercise: 3 stars, optional  *)
Lemma par_body_n : forall n st,
  st X = 0 /\ st Y = 0 ->
  exists st',
    par_loop / st ==>c*  par_loop / st' /\ st' X = n /\ st' Y = 0.
Proof.
  intros.
  inversion H.
  induction n.
  exists st.
  split.
  apply multi_refl.
  apply H.
  inversion IHn. clear IHn.
  inversion H2. clear H2.
  inversion H4.
  exists (update x X (S n)).
  split.
  apply par_body_n__Sn in H4.
  eapply multi_trans.
  apply H3.
  apply H4.
  split.
  unfold update.
  simpl.
  reflexivity.
  unfold update.
  simpl.
  apply H5.
Qed.

(*-- Check --*)
Check par_body_n : forall n st,
  st X = 0 /\ st Y = 0 ->
  exists st',
    par_loop / st ==>c*  par_loop / st' /\ st' X = n /\ st' Y = 0.

