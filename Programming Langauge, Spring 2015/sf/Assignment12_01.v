Require Export Assignment12_00.

(* problem #01: 10 points *)

(** **** Exercise: 3 stars, optional (typing_nonexample_3)  *)
(** Another nonexample:
    ~ (exists S, exists T,
          empty |- \x:S. x x : T).
*)

Lemma typing_sub0 :
  ~ (exists T1, exists T2, T1 = TArrow T1 T2).
Proof.
  intros Hc.
  inversion Hc as [T H].
  clear Hc.
  induction T.
  inversion H.
  inversion H0.
  apply IHT1. exists T2. apply H2.
  inversion H. inversion H0.
  inversion H. inversion H0.
  inversion H. inversion H0.
  inversion H. inversion H0.
  inversion H. inversion H0.
Qed.

Example typing_nonexample_3 :
  ~ (exists S, exists T,
        empty |- 
          (tabs X S
             (tapp (tvar X) (tvar X))) \in
          T).
Proof.
  unfold not.
  intros.
  inversion H.
  inversion H0.
  inversion H1; subst.
  inversion H7; subst.
  inversion H8; subst.
  inversion H5; subst.
  inversion H4.
  inversion H6.
  rewrite H3 in H9.
  apply typing_sub0.
  exists T1. exists T12.
  apply H9.
Qed.

(*-- Check --*)
Check typing_nonexample_3 :
  ~ (exists S, exists T,
        empty |- 
          (tabs X S
             (tapp (tvar X) (tvar X))) \in
          T).

