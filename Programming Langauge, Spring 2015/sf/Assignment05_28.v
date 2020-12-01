Require Export Assignment05_27.

(* problem #28: 30 points *)


(** 4 stars (palindromes)  *)
(** A palindrome is a sequence that reads the same backwards as
    forwards.

    - Define an inductive proposition [pal] on [list X] that
      captures what it means to be a palindrome. (Hint: You'll need
      three cases.  Your definition should be based on the structure
      of the list; just having a single constructor
        c : forall l, l = rev l -> pal l
      may seem obvious, but will not work very well.)
 
    - Prove [pal_app_rev] that 
       forall l, pal (l ++ rev l).
    - Prove [pal_rev] that 
       forall l, pal l -> l = rev l.
*)

Inductive pal {X: Type} : list X -> Prop :=
  | pal_0 : pal []
  | pal_1 : forall (x:X), pal [x]
  | pal_2 : forall (x:X) (l: list X), pal l -> pal (snoc (x::l) x)
.


Lemma pal_app_rev_sub1: forall (X: Type) (x: X) (l1 l2: list X),
  snoc (l1 ++ l2) x = l1 ++ snoc l2 x.
intros.
  induction l1.
  simpl.
  reflexivity.
  simpl.
  rewrite IHl1.
  reflexivity.
Qed.


Lemma pal_app_rev_sub0: forall (X: Type) (x: X) (l: list X),
  x :: l ++ snoc (rev l) x = snoc (x :: (l ++ (rev l))) x.
Proof.
  intros.
  induction l.
  simpl.
  reflexivity.
  inversion IHl.
  simpl.
  replace (l ++ snoc (snoc (rev l) x0) x) with (snoc (l ++ snoc (rev l) x0) x).
  reflexivity.
  rewrite pal_app_rev_sub1.
  reflexivity.
Qed.
  

Theorem pal_app_rev: forall (X: Type) (l: list X),
  pal (l ++ rev l).
Proof.
  intros.
  induction l.
  simpl.
  apply pal_0.
  simpl.
  rewrite pal_app_rev_sub0.
  apply pal_2.
  apply IHl.
Qed.




Lemma pal_rev_sub0: forall (X: Type) (x : X) (l: list X),
  rev (snoc l x) = x :: (rev l).
Proof.
  intros.
  induction l.
  simpl.
  reflexivity.
  simpl.
  rewrite IHl.
  simpl.
  reflexivity.
Qed.


Theorem pal_rev: forall (X: Type) (l: list X),
  pal l -> l = rev l.
Proof.
  intros.
  induction H.
  simpl.
  reflexivity.
  simpl.
  reflexivity.
  simpl.
  rewrite pal_rev_sub0.
  simpl.
  rewrite <- IHpal.
  reflexivity.
Qed.




(** [] *)




