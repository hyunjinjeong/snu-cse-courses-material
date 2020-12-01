Require Export Assignment08_03.

(* problem #04: 10 points *)

(** **** Exercise: 4 stars (no_whiles_terminating)  *)
(** Imp programs that don't involve while loops always terminate.
    State and prove a theorem [no_whiles_terminating] that says this. *)

(* Hint *)
Check andb_true_iff.

Theorem no_whiles_terminate: forall c st
    (NOWHL: no_whiles c = true),
  exists st', c / st || st'.
Proof.
  intros.
  generalize dependent st.
  induction c.
  intros.
  exists st.
  constructor.
  intros.
  exists (update st i (aeval st a)).
  constructor.
  reflexivity.
  intros.
  inversion NOWHL.
  apply andb_true_iff in H0.
  inversion H0.
  apply IHc1 with (st := st) in H.
  inversion H.
  apply IHc2 with (st := x) in H1.
  inversion H1.
  exists x0.
  apply E_Seq with x.
  apply H2.
  apply H3.
  intros.
  inversion NOWHL.
  apply andb_true_iff in H0.
  inversion H0.
  apply IHc1 with (st := st) in H.
  inversion H.
  apply IHc2 with (st := st) in H1.
  inversion H1.
  destruct (beval st b) eqn:myH.
  exists x.
  apply E_IfTrue.
  apply myH.
  apply H2.
  exists x0.
  apply E_IfFalse.
  apply myH.
  apply H3.
  intros.
  inversion NOWHL.
Qed.


(*-- Check --*)
Check no_whiles_terminate: forall c st
    (NOWHL: no_whiles c = true),
  exists st', c / st || st'.

