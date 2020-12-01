Require Export Assignment10_15.

(* problem #16: 10 points *)

(* Hint: 

   First study the chapter "Auto.v".

   Using [;], [try] and [eauto], you can prove it in 6 lines thanks to:
     Hint Constructors cstep.
 
   You can use the following intro pattern:
     destruct ... as [ | [? [? ?]]].
*)

Theorem cimp_strong_progress : forall c st,
  c = SKIP \/ 
  exists c' st', c / st ==>c c' / st'.
Proof.
  intros.
  induction c; try eauto; right.
  assert ((exists n, a = ANum n) \/ exists a', a / st ==>a a').
  apply aexp_strong_progress.
  inversion H.
  inversion H0.
  rewrite H1.
  exists SKIP. exists (update st i x).
  constructor.
  inversion H0.
  exists (i ::= x). exists st.
  constructor.
  apply H1.
  inversion IHc1.
  inversion IHc2.
  rewrite H. exists c2. exists st.
  constructor.
  inversion H0.
  inversion H1.
  rewrite H. exists c2. exists st.
  constructor.
  inversion H.
  inversion H0.
  inversion IHc2.
  exists (x ;; c2). exists x0.
  constructor.
  apply H1.
  inversion H2.
  inversion H3.
  exists (x ;; c2). exists x0.
  constructor.
  apply H1.

  assert ((b = BTrue \/ b = BFalse) \/ exists b', b / st ==>b b').
  apply bexp_strong_progress.
  inversion H.
  inversion H0.
  rewrite H1. exists c1. exists st.
  constructor.
  rewrite H1. exists c2. exists st.
  constructor.
  inversion H0.
  exists (IFB x THEN c1 ELSE c2 FI). exists st.
  constructor.
  apply H1.
  
  inversion IHc1.
  inversion IHc2.
  rewrite H. rewrite H0. exists SKIP. exists st.
  constructor.
  inversion H0.
  inversion H1.
  exists (PAR c1 WITH x END). exists x0.
  constructor.
  apply H2.
  inversion H.
  inversion H0.
  exists (PAR x WITH c2 END). exists x0.
  constructor.
  apply H1.
Qed.

(*-- Check --*)
Check cimp_strong_progress : forall c st,
  c = SKIP \/ 
  exists c' st', c / st ==>c c' / st'.

