Require Export Assignment10_09.

(* problem #10: 10 points *)

(** The fact that small-step reduction implies big-step is now
    straightforward to prove, once it is stated correctly. 

    The proof proceeds by induction on the multi-step reduction
    sequence that is buried in the hypothesis [normal_form_of t t']. *)
(** Make sure you understand the statement before you start to
    work on the proof.  *)

(** **** Exercise: 3 stars (multistep__eval)  *)

Theorem strong_progress : forall t,
  value t \/ (exists t', t ==> t').
Proof.  
  induction t.
  left. apply v_const.
  right. inversion IHt1.
  inversion IHt2.
  inversion H. inversion H0.
  exists (C (n + n0)).
  apply ST_PlusConstConst.
  inversion H0 as [t' H1].
  exists (P t1 t').
  apply ST_Plus2. apply H. apply H1.
  inversion H as [t' H0]. 
  exists (P t' t2).
  apply ST_Plus1. apply H0.
Qed.

Lemma nf_is_value : forall t,
  normal_form step t -> value t.
Proof. 
  unfold normal_form. intros t H.
  assert (G : value t \/ exists t', t ==> t').
  apply strong_progress.
  inversion G.
  apply H0.
  apply ex_falso_quodlibet. apply H. assumption.
Qed.

Theorem multistep__eval : forall t t',
  normal_form_of t t' -> exists n, t' = C n /\ t || n.
Proof.
  unfold normal_form_of.
  intros t t' [H0 H1].
  induction H0.
  apply nf_is_value in H1.
  inversion H1.
  subst.
  exists n.
  split.
  reflexivity.
  constructor.
  apply IHmulti in H1.
  destruct H1 as [n [H2 H3]].
  exists n.
  split.
  apply H2.
  eapply step__eval.
  apply H.
  apply H3.
Qed.

(*-- Check --*)
Check multistep__eval : forall t t',
  normal_form_of t t' -> exists n, t' = C n /\ t || n.

