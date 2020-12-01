Require Export Assignment07_02.

(* problem #03: 20 points *)

(** **** Exercise: 3 stars  (bevalR)  *)
(** Write a relation [bevalR] in the same style as
    [aevalR], and prove that it is equivalent to [beval].*)


Inductive bevalR: bexp -> bool -> Prop :=
  | E_BTrue: bevalR BTrue true
  | E_BFalse: bevalR BFalse false
  | E_BEq: forall (e1 e2: aexp) (n1 n2: nat),
           aevalR e1 n1 -> aevalR e2 n2 -> bevalR (BEq e1 e2) (beq_nat n1 n2) 
  | E_BLe: forall (e1 e2: aexp) (n1 n2: nat),
           aevalR e1 n1 -> aevalR e2 n2 -> bevalR (BLe e1 e2) (ble_nat n1 n2)
  | E_BNot: forall (e: bexp) (b: bool), bevalR e b -> bevalR (BNot e) (negb b)
  | E_BAnd: forall (e1 e2: bexp) (b1 b2: bool),
                   bevalR e1 b1 -> bevalR e2 b2 -> bevalR (BAnd e1 e2) (andb b1 b2)
.

Theorem beval_iff_bevalR : forall b bv,
  bevalR b bv <-> beval b = bv.
Proof.
split.
  intros h.
  induction h; simpl; try rewrite IHh; try reflexivity; try (apply aeval_iff_aevalR in H; apply aeval_iff_aevalR in H0; rewrite H; rewrite H0; reflexivity).
  rewrite IHh1; rewrite IHh2; reflexivity.
  generalize dependent bv.
  induction b; intros; try (rewrite <- H; constructor; apply aeval_iff_evalR).
  simpl in *. rewrite <- H. constructor. apply aeval_iff_aevalR. reflexivity.
  apply aeval_iff_aevalR. reflexivity. rewrite <- H. constructor.
  apply aeval_iff_aevalR. reflexivity. apply aeval_iff_aevalR. reflexivity.
  simpl in *. rewrite <- H. constructor. apply IHb. reflexivity.
  simpl in *. rewrite <- H. constructor. apply IHb1. reflexivity.
  simpl in *. apply IHb2. reflexivity.
Qed.

(** [] *)

