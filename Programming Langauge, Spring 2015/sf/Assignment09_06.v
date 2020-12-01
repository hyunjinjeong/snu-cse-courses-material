Require Export Assignment09_05.

(* problem #06: 10 points *)

(** **** Exercise: 2 stars (slow_assignment)  *)
(** A roundabout way of assigning a number currently stored in [X] to
    the variable [Y] is to start [Y] at [0], then decrement [X] until
    it hits [0], incrementing [Y] at each step. Here is a program that
    implements this idea:
      {{ X = m }}
    Y ::= 0;;
    WHILE X <> 0 DO
      X ::= X - 1;;
      Y ::= Y + 1
    END
      {{ Y = m }} 
    Write an informal decorated program showing that this is correct. *)

Lemma slow_ass_sub0: forall (n: nat) (m: nat),
  n <> 0 -> n + m = n - 1 + (m + 1).
Proof.
  unfold not.
  intros.
  induction n.
  assert (0 = 0).
  reflexivity.
  apply H in H0.
  inversion H0.
  simpl in *.
  assert ( n - 0 = n).
  omega.
  rewrite H0.
  omega.
Qed.

Theorem slow_assignment : forall m,
    {{ fun st => st X = m }}
    Y ::= ANum 0;;
    WHILE BNot (BEq (AId X) (ANum 0)) DO
      X ::= AMinus (AId X) (ANum 1);;
      Y ::= APlus (AId Y) (ANum 1)
    END
    {{ fun st => st Y = m }}.
Proof.
  intros.
  remember (BNot (BEq (AId X) (ANum 0))) as b.
  remember (X ::= AMinus (AId X) (ANum 1) ;; Y ::= APlus (AId Y) (ANum 1)) as c.
  apply hoare_seq with (Q := (fun st: state => st X + st Y = m)).
  remember (fun st: state => st X + st Y = m) as P.
  apply hoare_consequence_post with (Q' := fun st => (P st) /\ (beval st b = false)).
  apply hoare_while.
  subst.
  simpl.
  apply hoare_seq with (Q := (fun st: state => m = st X + (st Y + 1))).
  unfold hoare_triple.
  intros.
  inversion H.
  subst.
  unfold update.
  simpl in *.
  omega.
  unfold hoare_triple.
  intros.
  inversion H.
  subst.
  simpl.
  unfold update.
  simpl.
  inversion H0.
  subst.
  simpl in *.
  apply negb_true in H2. apply beq_nat_false in H2.
  apply slow_ass_sub0.
  apply H2.
  unfold assert_implies.
  intros.
  inversion H.
  subst.
  simpl in H1.
  apply negb_false in H1.
  apply beq_nat_true in H1.
  rewrite H1 in H0.
  simpl in H0.
  apply H0.
  unfold hoare_triple.
  intros.
  subst.
  inversion H.
  subst.
  unfold update.
  simpl.
  omega.
Qed.

(*-- Check --*)
Check slow_assignment : forall m,
    {{ fun st => st X = m }}
    Y ::= ANum 0;;
    WHILE BNot (BEq (AId X) (ANum 0)) DO
      X ::= AMinus (AId X) (ANum 1);;
      Y ::= APlus (AId Y) (ANum 1)
    END
    {{ fun st => st Y = m }}.
  
