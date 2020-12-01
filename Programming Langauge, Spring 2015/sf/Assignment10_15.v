Require Export Assignment10_14.

(* problem #15: 10 points *)

(* Hint: 

   First study the chapter "Auto.v".

   Using [;], [try] and [eauto], you can prove it in 7 lines thanks to:. 
     Hint Constructors bstep.

   You can use the following intro pattern:
     destruct ... as [[? | ?] | [? ?]].
*)

Theorem bexp_strong_progress: forall st b,
  (b = BTrue \/ b = BFalse) \/
  exists b', b / st ==>b b'.
Proof.
  intros.
  induction b; try eauto; right.
  assert ((exists n, a = ANum n) \/ exists a', a / st ==>a a').
  apply aexp_strong_progress.
  assert ((exists n, a0 = ANum n) \/ exists a', a0 / st ==>a a').
  apply aexp_strong_progress.
  inversion H.
  inversion H0.
  inversion H1.
  inversion H2.
  rewrite H3. rewrite H4. 
  exists (if (beq_nat x x0) then BTrue else BFalse).
  constructor.
  inversion H1.
  inversion H2.
  exists (BEq a x0).
  constructor.
  rewrite H3. constructor.
  apply H4.
  inversion H0.
  inversion H1.
  inversion H2.
  exists (BEq x a0).
  constructor.
  apply H3.
  inversion H1.
  inversion H2.
  exists (BEq x a0).
  constructor.
  apply H3.

  assert ((exists n, a = ANum n) \/ exists a', a / st ==>a a').
  apply aexp_strong_progress.
  assert ((exists n, a0 = ANum n) \/ exists a', a0 / st ==>a a').
  apply aexp_strong_progress.
  inversion H.
  inversion H0.
  inversion H1.
  inversion H2.
  rewrite H3. rewrite H4. 
  exists (if (ble_nat x x0) then BTrue else BFalse).
  constructor.
  inversion H1.
  inversion H2.
  exists (BLe a x0).
  constructor.
  rewrite H3. constructor.
  apply H4.
  inversion H0.
  inversion H1.
  inversion H2.
  exists (BLe x a0).
  constructor.
  apply H3.
  inversion H1.
  inversion H2.
  exists (BLe x a0).
  constructor.
  apply H3.
  
  inversion IHb.
  inversion H.
  rewrite H0.
  exists BFalse.
  constructor.
  rewrite H0.
  exists BTrue.
  constructor.
  inversion H.
  exists (BNot x).
  constructor.
  apply H0.
  inversion IHb1.
  inversion IHb2.
  inversion H.
  inversion H0.
  rewrite H1. rewrite H2.
  exists BTrue.
  constructor.
  rewrite H1. rewrite H2.
  exists BFalse.
  constructor.
  inversion H0.
  rewrite H1. rewrite H2.
  exists BFalse.
  constructor.
  rewrite H1. rewrite H2.
  exists BFalse. constructor.
  inversion H.
  inversion H0.
  rewrite H1.
  exists (BAnd BTrue x).
  constructor.
  apply H2.
  inversion H0.
  rewrite H1.
  exists BFalse.
  constructor.
  inversion H.
  inversion IHb2.
  inversion H1.
  exists (BAnd x b2).
  constructor.
  apply H0.
  exists (BAnd x b2).
  constructor.
  apply H0.
  inversion H1.
  exists (BAnd x b2).
  constructor.
  apply H0.
Qed.

(*-- Check --*)
Check bexp_strong_progress: forall st b,
  (b = BTrue \/ b = BFalse) \/
  exists b', b / st ==>b b'.

