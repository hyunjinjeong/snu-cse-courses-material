Require Export Assignment09_06.

(* problem #07: 10 points *)

(** **** Exercise: 3 stars, optional (add_slowly_decoration)  *)
(** The following program adds the variable X into the variable Z
    by repeatedly decrementing X and incrementing Z.
  WHILE X <> 0 DO
     Z ::= Z + 1;;
     X ::= X - 1
  END

    Following the pattern of the [subtract_slowly] example above, pick
    a precondition and postcondition that give an appropriate
    specification of [add_slowly]; then (informally) decorate the
    program accordingly. *)

Theorem slow_addition_dec_correct : forall n m,
  {{fun st => st X = n /\ st Y = m }}
  WHILE BNot (BEq (AId X) (ANum 0)) DO
     Y ::= APlus (AId Y) (ANum 1);;
     X ::= AMinus (AId X) (ANum 1)
  END
  {{fun st => st Y = n + m}}.
Proof.
   intros.
   remember (BNot (BEq (AId X) (ANum 0))) as b.
   remember (Y ::= APlus (AId Y) (ANum 1);; X ::= AMinus (AId X) (ANum 1)) as c.
   apply hoare_consequence_pre with (P' :=
   fun st: state => st X + st Y = n + m).
   remember (fun st: state => st X + st Y = n + m) as P.
   apply hoare_consequence_post with (Q' :=
   fun st: state => P st /\ beval st b = false).
   apply hoare_while.
   subst.
   simpl.
   unfold hoare_triple.
   intros.
   inversion H0.
   apply negb_true in H2. apply beq_nat_false in H2.
   inversion H.
   subst.
   inversion H5.
   inversion H8.
   subst.
   simpl in *.
   unfold update.
   simpl.
   omega.
   unfold assert_implies.
   intros.
   inversion H.
   subst.
   simpl in H1.
   apply negb_false in H1. apply beq_nat_true in H1.
   rewrite H1 in H0.
   simpl in H0.
   apply H0.
   unfold assert_implies.
   intros.
   subst.
   inversion H.
   rewrite H0. rewrite H1.
   reflexivity.
Qed.

(*-- Check --*)
Check slow_addition_dec_correct : forall n m,
  {{fun st => st X = n /\ st Y = m }}
  WHILE BNot (BEq (AId X) (ANum 0)) DO
     Y ::= APlus (AId Y) (ANum 1);;
     X ::= AMinus (AId X) (ANum 1)
  END
  {{fun st => st Y = n + m}}.

