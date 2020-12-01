Require Export Assignment12_05.

(* problem #06: 10 points *)


Notation TA := (tapp tloop (tnat 0)).
Notation TB := (tapp
       (tapp
          (tabs Loop (TArrow TNat TNat)
             (tabs X TNat (tapp (tvar Loop) (tvar X)))) tloop) (tnat 0)).

Notation TC := (tapp ([Loop := tloop]tabs X TNat (tapp (tvar Loop) (tvar X))) (tnat 0)).

Lemma AtoB:
  TA ==> TB.
Proof.
  unfold tloop.
  eauto.
Qed.

Lemma BtoC:
  TB ==> TC.
Proof.
  unfold tloop.
  eauto.
Qed.

Lemma CtoA:
  TC ==> TA.
Proof.
  unfold tloop.
  constructor.
  eauto.
Qed.

Lemma TAsame: forall t,
  TA ==> t -> t = TB.
Proof.
  intros.
  inversion H; subst.
  inversion H3; subst.
  inversion H1.
  inversion H4.
  reflexivity.
Qed.

Lemma TBsame: forall t,
  TB ==> t -> t = TC.
Proof.
  intros.
  inversion H; subst.
  inversion H3; subst.
  reflexivity.
  inversion H4; subst.
  inversion H5; subst.
  inversion H1.
  inversion H4.
Qed.

Lemma TCsame: forall t,
  TC ==> t -> t = TA.
Proof.
  intros.
  inversion H; subst.
  auto.
  inversion H3.
  inversion H4.
Qed.
 
Inductive nodap: tm -> nat -> tm -> Prop :=
  | nodap0 : forall (t: tm), nodap t 0 t
  | nodap1 : forall (t t2 t3: tm) (n: nat), t ==> t2 -> nodap t2 n t3 -> nodap t (S n) t3
.

Lemma sub1: forall (t t1: tm),
  t ==>* t1 -> exists (n: nat), nodap t n t1.
Proof.
  intros.
  induction H.
  exists 0. constructor.
  inversion IHmulti; subst.
  exists (S x0).
  eapply nodap1.
  apply H.
  apply H1.
Qed.


Lemma sub2: forall (n: nat) (x: tm),
 nodap TA n x \/ nodap TB n x \/ nodap TC n x -> x = TA \/ x = TB \/ x = TC.
Proof.
  intro. induction n; intros.
  inversion H.
  inversion H0.
  left. reflexivity.
  inversion H0.
  right. left. inversion H1. reflexivity.
  right. right. inversion H1. reflexivity.
  inversion H. inversion H0; subst.
  assert (t2 = TB). apply TAsame. apply H2. subst.
  apply IHn. right. left. apply H4.
  inversion H0. inversion H1; subst.
  assert (t2 = TC). apply TBsame. apply H3. subst.
  apply IHn. right. right. apply H5.
  inversion H1; subst. assert (t2 = TA). apply TCsame. apply H3. subst.
  apply IHn. left. apply H5.
Qed.


Lemma sub0: forall (x: tm),
  TA ==>* x -> x = TA \/ x = TB \/ x = TC.
Proof.
  intros.
  apply sub1 in H. inversion H.
  apply sub2 with (n := x0).
  left. apply H0.
Qed.

Theorem tloop_diverges:
  ~ exists t, tapp tloop (tnat 0) ==>* t /\ normal_form step t.
Proof.
  unfold normal_form.
  unfold not.
  intros.
  inversion H. inversion H0.
  assert (TA ==>* x -> x = TA \/ x = TB \/ x = TC).
  apply sub0.
  apply H3 in H1.
  inversion H1; subst.
  assert (exists t': tm, TA ==> t').
  exists TB. apply AtoB.
  apply H2 in H4. apply H4.
  inversion H4; subst.
  apply H2. exists TC. apply BtoC.
  apply H2. exists TA. apply CtoA.
Qed.


(*-- Check --*)
Check tloop_diverges:
  ~ exists t, tapp tloop (tnat 0) ==>* t /\ normal_form step t.