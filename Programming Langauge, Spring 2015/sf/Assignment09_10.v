Require Export Assignment09_09.

(* problem #10: 10 points *)

(** **** Exercise: 3 stars (two_loops)  *)
(** Here is a very inefficient way of adding 3 numbers:
  X ::= 0;;
  Y ::= 0;;
  Z ::= c;;
  WHILE X <> a DO
    X ::= X + 1;;
    Z ::= Z + 1
  END;;
  WHILE Y <> b DO
    Y ::= Y + 1;;
    Z ::= Z + 1
  END

    Show that it does what it should by filling in the blanks in the
    following decorated program.

    {{ True }} ->>
    {{                                        }}
  X ::= 0;;
    {{                                        }}
  Y ::= 0;;
    {{                                        }}
  Z ::= c;;
    {{                                        }}
  WHILE X <> a DO
      {{                                        }} ->>
      {{                                        }}
    X ::= X + 1;;
      {{                                        }}
    Z ::= Z + 1
      {{                                        }}
  END;;
    {{                                        }} ->>
    {{                                        }}
  WHILE Y <> b DO
      {{                                        }} ->>
      {{                                        }}
    Y ::= Y + 1;;
      {{                                        }}
    Z ::= Z + 1
      {{                                        }}
  END
    {{                                        }} ->>
    {{ Z = a + b + c }}
*)

Theorem add_three_numbers_correct: forall a b c,
  {{ fun st => True }}                                   
  X ::= ANum 0;;
  Y ::= ANum 0;;
  Z ::= ANum c;;
  WHILE BNot (BEq (AId X) (ANum a)) DO
    X ::= APlus (AId X) (ANum 1);;
    Z ::= APlus (AId Z) (ANum 1)
  END;;
  WHILE BNot (BEq (AId Y) (ANum b)) DO
    Y ::= APlus (AId Y) (ANum 1);;
    Z ::= APlus (AId Z) (ANum 1)
  END
  {{ fun st => st Z = a + b + c }}.
Proof.
  intros.
  remember (BNot (BEq (AId X) (ANum a))) as b1.
  remember (X ::= APlus (AId X) (ANum 1) ;; Z ::= APlus (AId Z) (ANum 1)) as c1.
  remember (BNot (BEq (AId Y) (ANum b))) as b2.
  remember (Y ::= APlus (AId Y) (ANum 1) ;; Z ::= APlus (AId Z) (ANum 1)) as c2.
  apply hoare_seq with (Q := ((fun st : state => st Z = st X + st Y + c) [Z |-> ANum c]) [ Y |-> ANum 0]).
  apply hoare_seq with (Q := (fun st: state => st Z = st X + st Y + c) [ Z |-> ANum c]  ).
  apply hoare_seq with (Q := fun st: state => st Z = st X + st Y + c).
  apply hoare_seq with (Q := fun st: state => st Z = a + st Y + c).
  remember (fun st: state => st Z = a + st Y + c) as P.
  apply hoare_consequence_post with (Q' :=
  fun st: state => P st /\ beval st b2 = false).
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
  rewrite H1.
  omega.
  subst.
  simpl.
  unfold assert_implies.
  intros.
  inversion H.
  apply negb_false in H1. apply beq_nat_true in H1.
  rewrite H1 in H0.
  apply H0.
  subst.
  remember (fun st: state => st Z = st X + st Y + c) as P.
  apply hoare_consequence_post with (Q' :=
  fun st: state => P st /\ beval st (BNot (BEq (AId X) (ANum a))) = false).
  apply hoare_while.
  simpl in *.
  unfold hoare_triple.
  intros.
  subst.
  inversion H.
  subst.
  inversion H3.
  subst.
  inversion H6.
  subst.
  unfold update in *.
  simpl in *.
  inversion H0.
  apply negb_true in H2. apply beq_nat_false in H2.
  rewrite H1.
  omega.
  subst.
  simpl.
  unfold assert_implies.
  intros.
  inversion H.
  rewrite H0.
  apply negb_false in H1. apply beq_nat_true in H1.
  rewrite H1.
  reflexivity.
  subst.
  apply hoare_asgn.
  apply hoare_asgn.
  apply hoare_consequence_pre with (P' :=
  (((fun st: state => st Z = st X + st Y + c) [Z |-> ANum c]) [Y |-> ANum 0]) [X |-> ANum 0]).
  apply hoare_asgn.
  unfold assert_implies.
  intros.
  subst.
  unfold assn_sub.
  simpl.
  unfold update.
  simpl.
  reflexivity.
Qed.

(*-- Check --*)
Check add_three_numbers_correct: forall a b c,
  {{ fun st => True }}                                   
  X ::= ANum 0;;
  Y ::= ANum 0;;
  Z ::= ANum c;;
  WHILE BNot (BEq (AId X) (ANum a)) DO
    X ::= APlus (AId X) (ANum 1);;
    Z ::= APlus (AId Z) (ANum 1)
  END;;
  WHILE BNot (BEq (AId Y) (ANum b)) DO
    Y ::= APlus (AId Y) (ANum 1);;
    Z ::= APlus (AId Z) (ANum 1)
  END
  {{ fun st => st Z = a + b + c }}.

