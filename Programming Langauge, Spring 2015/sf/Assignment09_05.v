Require Export Assignment09_04.

(* problem #05: 10 points *)

(** **** Exercise: 2 stars (if_minus_plus)  *)
(** Prove the following hoare triple using [hoare_if]: *)

Theorem if_minus_plus :
  {{fun st => True}}
  IFB (BLe (AId X) (AId Y))
    THEN (Z ::= AMinus (AId Y) (AId X))
    ELSE (Y ::= APlus (AId X) (AId Z))
  FI
  {{fun st => st Y = st X + st Z}}. 
Proof.
  remember (BLe (AId X) (AId Y)) as b.
  remember (Z ::= AMinus (AId Y) (AId X)) as c1.
  remember (Y ::= APlus (AId X) (AId Z)) as c2.
  remember (fun (st: state) => st Y = st X + st Z) as Q.
  apply hoare_consequence_pre with
  (P' := fun st => (beval st b = true -> (Q [ Z |-> AMinus (AId Y) (AId X)]) st) /\ (beval st b = false -> (Q [ Y |-> APlus (AId X) (AId Z) ]) st)).
  apply hoare_if.
  rewrite Heqc1.
  apply hoare_asgn.
  rewrite Heqc2.
  apply hoare_asgn.
  split.
  intros.
  unfold assn_sub.
  simpl in *.
  subst.
  simpl in *.
  apply ble_nat_true in H0.
  unfold update.
  simpl.
  omega.
  intros.
  unfold assn_sub.
  simpl.
  subst.
  unfold update.
  simpl.
  omega.
Qed.

(*-- Check --*)
Check if_minus_plus :
  {{fun st => True}}
  IFB (BLe (AId X) (AId Y))
    THEN (Z ::= AMinus (AId Y) (AId X))
    ELSE (Y ::= APlus (AId X) (AId Z))
  FI
  {{fun st => st Y = st X + st Z}}. 

