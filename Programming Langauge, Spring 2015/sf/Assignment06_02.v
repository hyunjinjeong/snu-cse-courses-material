Require Export Assignment06_01.

(* problem #02: 10 points *)

(** **** Exercise: 3 stars, optional (not_exists_dist)  *)
(** (The other direction of this theorem requires the classical "law
    of the excluded middle".) *)

Theorem not_exists_dist :
  excluded_middle ->
  forall (X:Type) (P : X -> Prop),
    ~ (exists x, ~ P x) -> (forall x, P x).
Proof.
  unfold not.
  intros.
  assert (P x \/ ~ P x).
  apply H.
  unfold not in H1.
  inversion H1.
  apply H2.
  assert ( False -> P x).
  intros.
  inversion H3.
  apply H3.
  apply H0.
  exists x.
  apply H2.
Qed.
(** [] *)

