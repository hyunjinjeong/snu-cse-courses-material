Require Export Assignment05_03.

(* problem #04: 10 points *)



Theorem iff_trans : forall P Q R : Prop, 
  (P <-> Q) -> (Q <-> R) -> (P <-> R).
Proof.
  intros.
  inversion H.
  inversion H0.
  split.
  intros.
  apply H3.
  apply H1.
  apply H5.
  intros.
  apply H2.
  apply H4.
  apply H5.
Qed.


