Require Export Assignment10_13.

(* problem #14: 10 points *)

(* Hint: 

   First study the chapter "Auto.v".

   Using [;], [try] and [eauto], you can prove it in 4 lines thanks to: 
     Hint Constructors aval
     Hint Constructors astep.
  
   You can use the following intro pattern:
     destruct ... as [[? ?] | [? ?]].
*)

Theorem aexp_strong_progress: forall st a,
  (exists n, a = ANum n) \/
  exists a', a / st ==>a a'.
Proof.
  induction a; try eauto.
  inversion IHa1.
  inversion H.
  inversion IHa2.
  inversion H1.
  right.
  exists (ANum (x+x0)).
  rewrite H0. rewrite H2. constructor.
  inversion H1.
  right.
  exists (APlus a1 x0).
  apply AS_Plus2.
  rewrite H0. constructor. apply H2.
  inversion H.
  inversion IHa2.
  right.
  inversion H1.
  exists (APlus x a2).
  rewrite H2.
  constructor.
  apply H0.
  inversion H1.
  right.
  exists (APlus x a2).
  constructor.
  apply H0.
  
inversion IHa1.
  inversion H.
  inversion IHa2.
  inversion H1.
  right.
  exists (ANum (x-x0)).
  rewrite H0. rewrite H2. constructor.
  inversion H1.
  right.
  exists (AMinus a1 x0).
  apply AS_Minus2.
  rewrite H0. constructor. apply H2.
  inversion H.
  inversion IHa2.
  right.
  inversion H1.
  exists (AMinus x a2).
  rewrite H2.
  constructor.
  apply H0.
  inversion H1.
  right.
  exists (AMinus x a2).
  constructor.
  apply H0.

inversion IHa1.
  inversion H.
  inversion IHa2.
  inversion H1.
  right.
  exists (ANum (x*x0)).
  rewrite H0. rewrite H2. constructor.
  inversion H1.
  right.
  exists (AMult a1 x0).
  apply AS_Mult2.
  rewrite H0. constructor. apply H2.
  inversion H.
  inversion IHa2.
  right.
  inversion H1.
  exists (AMult x a2).
  rewrite H2.
  constructor.
  apply H0.
  inversion H1.
  right.
  exists (AMult x a2).
  constructor.
  apply H0.
Qed.

(*-- Check --*)
Check aexp_strong_progress: forall st a,
  (exists n, a = ANum n) \/
  exists a', a / st ==>a a'.

