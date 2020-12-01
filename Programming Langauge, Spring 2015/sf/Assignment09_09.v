Require Export Assignment09_08.

(* problem #09: 10 points *)

(** **** Exercise: 4 stars (factorial)  *)
(** Recall that [n!] denotes the factorial of [n] (i.e. [n! =
    1*2*...*n]).  Here is an Imp program that calculates the factorial
    of the number initially stored in the variable [X] and puts it in
    the variable [Y]:
    {{ X = m }} 
  Y ::= 1 ;;
  WHILE X <> 0
  DO
     Y ::= Y * X ;;
     X ::= X - 1
  END
    {{ Y = m! }}

    Fill in the blanks in following decorated program:
    {{ X = m }} ->>
    {{                                      }}
  Y ::= 1;;
    {{                                      }}
  WHILE X <> 0
  DO   {{                                      }} ->>
       {{                                      }}
     Y ::= Y * X;;
       {{                                      }}
     X ::= X - 1
       {{                                      }}
  END
    {{                                      }} ->>
    {{ Y = m! }}
*)

Print fact.

Lemma facto_sub0: forall n: nat,
  n <> 0 -> n * fact (n - 1) = fact n.
Proof.
  unfold not.
  intros.
  induction n.
  simpl.
  assert ( 0 = 0).
  reflexivity.
  apply H in H0.
  inversion H0.
  simpl in *.
  assert ( n - 0 = n ).
  omega.
  rewrite H0.
  reflexivity.
Qed.
  


Theorem factorial_dec_correct: forall m,
  {{ fun st => st X = m }} 
  Y ::= ANum 1 ;;
  WHILE BNot (BEq (AId X) (ANum 0))
  DO
     Y ::= AMult (AId Y) (AId X) ;;
     X ::= AMinus (AId X) (ANum 1)
  END
  {{ fun st => st Y = fact m }}.
Proof.
  intros.
  remember (BNot (BEq (AId X) (ANum 0))) as b.
  remember (Y ::= AMult (AId Y) (AId X);; X ::= AMinus (AId X) (ANum 1)) as c.
  apply hoare_seq with (Q := (fun st: state => fact (st X) * st Y = fact m)).
  remember (fun st: state => fact (st X) * st Y = fact m) as P.
  apply hoare_consequence_post with (Q' :=
  fun st: state => P st /\ beval st b = false).
  apply hoare_while.
  subst.
  simpl.
  unfold hoare_triple.
  intros.
  inversion H.
  subst.
  inversion H3.
  subst.
  inversion H6.
  subst.
  unfold update in *.
  simpl in *.
  inversion H0.
  rewrite <- H1.
  apply negb_true in H2. apply beq_nat_false in H2.
  rewrite mult_assoc.
  rewrite mult_comm.
  rewrite mult_assoc.
  apply facto_sub0 in H2.
  rewrite H2.
  reflexivity.
  unfold assert_implies.
  intros.
  inversion H.
  subst.
  simpl in *.
  apply negb_false in H1. apply beq_nat_true in H1.
  rewrite H1 in H0.
  simpl in H0.
  rewrite <- H0.
  omega.
  unfold hoare_triple.
  intros.
  subst.
  inversion H.
  subst.
  simpl.
  unfold update.
  simpl.
  omega.
Qed.



(*-- Check --*)
Check factorial_dec_correct: forall m,
  {{ fun st => st X = m }} 
  Y ::= ANum 1 ;;
  WHILE BNot (BEq (AId X) (ANum 0))
  DO
     Y ::= AMult (AId Y) (AId X) ;;
     X ::= AMinus (AId X) (ANum 1)
  END
  {{ fun st => st Y = fact m }}.

