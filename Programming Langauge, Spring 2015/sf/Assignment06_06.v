Require Export Assignment06_05.

(* problem #06: 20 points *)

(** **** Exercise: 4 stars, advanced (no_repeats)  *)
(** The following inductively defined proposition... *)

Inductive appears_in {X:Type} (a:X) : list X -> Prop :=
  | ai_here : forall l, appears_in a (a::l)
  | ai_later : forall b l, appears_in a l -> appears_in a (b::l).

(** ...gives us a precise way of saying that a value [a] appears at
    least once as a member of a list [l]. 

    Here's a pair of warm-ups about [appears_in].
*)

Lemma appears_in_app : forall (X:Type) (xs ys : list X) (x:X), 
     appears_in x (xs ++ ys) -> appears_in x xs \/ appears_in x ys.
Proof.
  induction xs.
  simpl.
  intros.
  right.
  apply H.
  simpl.
  intros.
  inversion H.
  left.
  apply ai_here.
  apply IHxs in H1.
  inversion H1.
  left.
  apply ai_later.
  apply H3.
  right.
  apply H3.
Qed.


Lemma app_appears_in_sub0 : forall (X:Type) (xs ys : list X) (x:X),
  appears_in x xs -> appears_in x (xs++ys).
Proof.
  intros X xs.
  induction xs.
  simpl.
  intros.
  inversion H.
  simpl.
  intros.
  inversion H.
  apply ai_here.
  apply ai_later.
  apply IHxs.
  apply H1.
Qed.
  
Lemma app_appears_in_sub1 : forall (X:Type) (xs ys : list X) (x:X),
  appears_in x ys -> appears_in x (xs++ys).
Proof.
  intros.
  induction xs.
  simpl.
  apply H.
  simpl.
  apply ai_later.
  apply IHxs.
Qed.

Lemma app_appears_in : forall (X:Type) (xs ys : list X) (x:X), 
     appears_in x xs \/ appears_in x ys -> appears_in x (xs ++ ys).
Proof.
  intros.
  induction H.
  apply app_appears_in_sub0.
  apply H.
  apply app_appears_in_sub1.
  apply H.
Qed.

