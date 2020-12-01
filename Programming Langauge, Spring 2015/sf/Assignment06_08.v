Require Export Assignment06_07.

(* problem #08: 40 points *)

(** **** Exercise: 4 stars, advanced (pigeonhole principle)  *)
(** The "pigeonhole principle" states a basic fact about counting:
   if you distribute more than [n] items into [n] pigeonholes, some 
   pigeonhole must contain at least two items.  As is often the case,
   this apparently trivial fact about numbers requires non-trivial
   machinery to prove, but we now have enough... *)

(** First a pair of useful lemmas (we already proved these for lists
    of naturals, but not for arbitrary lists). *)

Lemma app_length : forall (X:Type) (l1 l2 : list X),
  length (l1 ++ l2) = length l1 + length l2. 
Proof. 
  intros.
  induction l1.
  simpl.
  reflexivity.
  simpl.
  rewrite IHl1.
  reflexivity.
Qed.

Lemma appears_in_app_split : forall (X:Type) (x:X) (l:list X),
  appears_in x l -> 
  exists l1, exists l2, l = l1 ++ (x::l2).
Proof.
  intros.
  induction H.
  exists [].
  exists l.
  reflexivity.
  inversion IHappears_in.
  inversion proof.
  rewrite proof0.
  exists (b::witness).
  exists witness0.
  reflexivity.
Qed.

(** Now define a predicate [repeats] (analogous to [no_repeats] in the
   exercise above), such that [repeats X l] asserts that [l] contains
   at least one repeated element (of type [X]).  *)

Inductive repeats {X:Type} : list X -> Prop :=
  | rep_here : forall (x:X) (l: list X), appears_in x l -> repeats (x::l)
  | rep_later : forall (x:X) (l: list X), repeats l -> repeats (x::l)
.

(** Now here's a way to formalize the pigeonhole principle. List [l2]
    represents a list of pigeonhole labels, and list [l1] represents
    the labels assigned to a list of items: if there are more items
    than labels, at least two items must have the same label.  This
    proof is much easier if you use the [excluded_middle] hypothesis
    to show that [appears_in] is decidable, i.e. [forall x
    l, (appears_in x l) \/ ~ (appears_in x l)].  However, it is also
    possible to make the proof go through _without_ assuming that
    [appears_in] is decidable; if you can manage to do this, you will
    not need the [excluded_middle] hypothesis. *)


Lemma length_plus_1 : forall (X:Type) (l1 l2 : list X),
  length l1 + S (length l2) = S (length l1 + length l2).
Proof.
  intros.
  induction l1.
  simpl.
  reflexivity.
  simpl.
  rewrite IHl1.
  reflexivity.
Qed.


Lemma test : forall (P1: Prop),
  excluded_middle -> P1 /\ ~P1 -> False.
Proof.
  intros.
  inversion H0.
  unfold not in H2.
  apply H2.
  apply H1.
Qed.

Lemma test2: forall (X: Type) (x x0: X) (l1 l2: list X),
  x <> x0 -> appears_in x0 (l1 ++ x :: l2) -> appears_in x0 (l1 ++ l2).
Proof.
  intros.
  unfold not in H.
  apply appears_in_app in H0.
  inversion H0.
  apply app_appears_in.
  left.
  apply H1.
  induction l1.
  simpl.
  inversion H1.
  symmetry in H3.
  apply H in H3.
  inversion H3.
  apply H3.
  simpl.
  apply ai_later.
  apply IHl1.
  right.
  apply H1.
Qed.

Theorem pigeonhole_principle: forall (X:Type) (l1  l2:list X), 
   excluded_middle -> 
   (forall x, appears_in x l1 -> appears_in x l2) -> 
   length l2 < length l1 -> 
   repeats l1.  
Proof.
   intros X l1. induction l1 as [|x l1'].
   simpl.
   intros.
   inversion H1.
   simpl.
   intros.
   assert (appears_in x l1' \/ ~ appears_in x l1').
     apply H.
   inversion H2.
   apply rep_here.
   apply H3.
   unfold not in H3.
   apply rep_later.
   assert (appears_in x (x :: l1')).
     apply ai_here.
   apply H0 in H4.
   apply appears_in_app_split in H4.
   inversion H4.
   inversion proof.
   rewrite proof0 in H1.
   rewrite app_length in H1.
   simpl in H1.
   rewrite length_plus_1 in H1.
   rewrite <- app_length in H1.
   apply Sn_le_Sm__n_le_m in H1.
   assert ( length (witness ++ witness0) < length l1').
     unfold lt.
     apply H1.
   rewrite proof0 in H0.
   apply IHl1' with (l2 := (witness ++ witness0)).
   apply H.
   intros.
   assert (appears_in x0 l1').
   apply H6.
   apply ai_later with (b:= x)  in H7.
   inversion H7.
   rewrite H9 in H7.
   assert (False).
     apply test with (P1:= appears_in x l1').
     apply H.
     split.
     rewrite H9 in H6.
     apply H6.
     unfold not.
     apply H3.
   inversion H8.
   apply H0 in H7.
   apply test2 in H7.
   apply H7.
   unfold not.
   intros.
   rewrite <- H11 in H6.
   assert (False).
     apply test with (P1:= appears_in x l1').
     apply H.
     split.
     apply H6.
     unfold not.
     apply H3.
     apply H12.
   apply H5.
Qed.



