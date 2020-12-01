Require Export Assignment10_05.

(* problem #06: 10 points *)

Theorem normal_forms_unique:
  deterministic normal_form_of.
Proof.
  unfold deterministic. unfold normal_form_of.  intros x y1 y2 P1 P2.
  inversion P1 as [P11 P12]; clear P1. inversion P2 as [P21 P22]; clear P2. 
  generalize dependent y2. 
  (* We recommend using this initial setup as-is! *)
  unfold step_normal_form in *.
  unfold normal_form in *.
  unfold not in *.
  induction P11.
  intros.
  inversion P21.
  reflexivity.
  subst.
  assert (exists t' : tm, x ==> t').
  exists y.
  apply H.
  apply P12 in H1.
  inversion H1.
  intros.
  inversion P21.
  subst.
  assert (exists t' : tm, y2 ==> t').
  exists y.
  apply H.
  apply P22 in H0.
  inversion H0.
  subst.
  apply IHP11.
  apply P12.
  assert (y = y0).
  apply step_deterministic_alt with (x := x).
  apply H.
  apply H0.
  rewrite H2.
  apply H1.
  apply P22.
Qed.

(*-- Check --*)
Check normal_forms_unique:
  deterministic normal_form_of.

