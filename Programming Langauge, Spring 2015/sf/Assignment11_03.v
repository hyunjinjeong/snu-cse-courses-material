Require Export Assignment11_02.

(* problem #03: 10 points *)

(** **** Exercise: 3 stars, optional (step_deterministic)  *)
(** Using [value_is_nf], we can show that the [step] relation is
    also deterministic... *)

Theorem step_deterministic:
  deterministic step.
Proof with eauto.
  unfold deterministic.
  intros.
  generalize dependent y2.
  induction H; intros.
  inversion H0;
  subst.
  reflexivity.
  inversion H4.
  inversion H0;
  subst.
  reflexivity.
  inversion H4.
  inversion H0;
  subst.
  inversion H.
  inversion H.
  apply IHstep in H5.
  subst.
  reflexivity.
  inversion H0;
  subst.
  apply IHstep in H2. subst. reflexivity.
  inversion H0; subst.
  reflexivity.
  inversion H1.
  inversion H0;subst.
  reflexivity.
  assert (step_normal_form (tsucc t1)).
  apply value_is_nf.
  right.
  constructor. apply H.
  unfold normal_form in H1. unfold not in H1.
  assert (exists t': tm, tsucc t1 ==> t').
  exists t1'. apply H2. apply H1 in H3.
  inversion H3.
  inversion H0; subst.
  inversion H.
  assert (step_normal_form (tsucc y2)).
  apply value_is_nf.
  right. constructor. apply H2.
  unfold normal_form in H1. unfold not in H1.
  assert (exists t': tm, tsucc y2 ==> t').
  exists t1'. apply H. apply H1 in H3. inversion H3.
  apply IHstep in H2. subst. reflexivity.
  inversion H0.
  reflexivity.
  subst.
  inversion H1.
  inversion H0.
  reflexivity.
  subst.
  assert (step_normal_form (tsucc t1)).
  apply value_is_nf. right. constructor. apply H.
  unfold normal_form in H1. unfold not in H1.
  assert (exists t': tm, tsucc t1 ==> t').
  exists t1'. apply H2. apply H1 in H3.
  inversion H3.
  inversion H0; subst.
  inversion H.
  assert (step_normal_form (tsucc t0)).
  apply value_is_nf. right. constructor. apply H2.
  unfold normal_form in H1. unfold not in H1.
  assert (exists t': tm, tsucc t0 ==> t').
  exists t1'. apply H. apply H1 in H3.
  inversion H3.
  apply IHstep in H2. subst.
  reflexivity.
Qed.

(*-- Check --*)
Check step_deterministic:
  deterministic step.

