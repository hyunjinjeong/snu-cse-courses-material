Require Export Assignment11_01.

(* problem #02: 10 points *)

(** **** Exercise: 3 stars, advanced (value_is_nf)  *)
(** Hint: You will reach a point in this proof where you need to
    use an induction to reason about a term that is known to be a
    numeric value.  This induction can be performed either over the
    term itself or over the evidence that it is a numeric value.  The
    proof goes through in either case, but you will find that one way
    is quite a bit shorter than the other.  For the sake of the
    exercise, try to complete the proof both ways. *)

Lemma value_is_nf : forall t,
  value t -> step_normal_form t.
Proof.
  intros.
  inversion H.
  induction H0;
  unfold normal_form;
  unfold not; intros;
  inversion H0;
  inversion H1.
  induction H0.
  unfold normal_form. unfold not. intros.
  inversion H0. inversion H1.
  assert ( nvalue t -> value t).
  intros. right. apply H1.
  apply H1 in H0.
  apply IHnvalue in H0.
  unfold normal_form in *. unfold not in *.
  intros.
  inversion H2.
  clear H1.
  clear H2.
  apply H0.
  exists x.
  inversion H3.
  subst.
  assert (exists t': tm, t ==> t').
  exists t1'.
  apply H2.
  apply H0 in H1.
  inversion H1.
Qed.

(*-- Check --*)
Check value_is_nf : forall t,
  value t -> step_normal_form t.

