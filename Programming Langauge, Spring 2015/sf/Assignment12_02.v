Require Export Assignment12_01.

(* problem #02: 10 points *)

(** **** Exercise: 2 stars, optional (typable_empty__closed)  *)
Corollary typable_empty__closed : forall t T, 
    empty |- t \in T  ->
    closed t.
Proof.
  intros. unfold closed. unfold not.
  intros.
  apply free_in_context with (T := T) (Gamma := empty) in H0.
  inversion H0.
  inversion H1.
  apply H.
Qed.

(*-- Check --*)
Check typable_empty__closed : forall t T, 
    empty |- t \in T  ->
    closed t.
