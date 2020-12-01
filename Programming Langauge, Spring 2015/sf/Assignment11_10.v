Require Export Assignment11_09.

(* problem #10: 30 points *)

(** Write a type checking function [tyeq: tm -> ty -> bool].
**)

Fixpoint tycheck (t: tm) (T: ty) : bool :=
  match t with
  | ttrue | tfalse => match T with
                      | TNat => false
                      | TBool => true
                      end
  | tzero => match T with
             | TNat => true
             | TBool => false
             end
  | tiszero t' => match T with
                  | TNat => false
                  | TBool => tycheck t' TNat
                  end
  | tsucc t' => match T with
                | TNat => tycheck t' TNat
                | TBool => false
                end
  | tpred t' => match T with
                | TNat => tycheck t' TNat
                | TBool => false
                end
  | tif t1 t2 t3 => andb (tycheck t1 TBool) (andb (tycheck t2 T) (tycheck t3 T))
  end.

Example tycheck_ex1:
  tycheck
    (tif (tiszero (tpred (tsucc (tsucc tzero)))) ttrue (tiszero (tsucc tzero))) 
    TBool 
  = true.
Proof. simpl. reflexivity. Qed.

Example tycheck_ex2:
  tycheck
    (tif (tiszero (tpred (tsucc (tsucc tzero)))) tzero (tiszero (tsucc tzero))) 
    TBool 
  = false.
Proof. simpl. reflexivity. Qed.

(** Prove that the type checking function [tyeq: tm -> ty -> bool] is correct.

    Hint: use the lemma [andb_prop].
**)

Check andb_prop.

Theorem tycheck_correct1: forall t T
    (TYCHK: tycheck t T = true),
  |- t \in T.
Proof.
  intros. generalize dependent T. 
  induction t; intros; destruct T.
  constructor. simpl in TYCHK. inversion TYCHK.
  constructor. simpl in TYCHK. inversion TYCHK.
  simpl in TYCHK. apply andb_prop in TYCHK.
  destruct TYCHK. apply andb_prop in H0. destruct H0.
  apply IHt1 in H. apply IHt2 in H0. apply IHt3 in H1.
  constructor. apply H. apply H0. apply H1.
  simpl in TYCHK. apply andb_prop in TYCHK.
  destruct TYCHK. apply andb_prop in H0. destruct H0.
  apply IHt2 in H0. apply IHt3 in H1.
  constructor; try apply H0; try apply H1.
  apply IHt1 in H. apply H. simpl in TYCHK.
  inversion TYCHK. constructor.
  simpl in TYCHK. inversion TYCHK. constructor.
  simpl in TYCHK. apply IHt in TYCHK. apply TYCHK.
  simpl in TYCHK. inversion TYCHK. simpl in TYCHK.
  apply IHt in TYCHK. constructor. apply TYCHK.
  constructor. simpl in TYCHK. apply IHt in TYCHK. apply TYCHK.
  simpl in TYCHK. inversion TYCHK.
Qed.

Theorem tycheck_correct2: forall t T
    (HASTY: |- t \in T),
  tycheck t T = true.
Proof.
  intros. generalize dependent T.
  induction t; intros; destruct T.
  simpl. reflexivity. inversion HASTY.
  simpl. reflexivity. inversion HASTY.
  simpl. inversion HASTY; subst.
  apply IHt1 in H2. apply IHt2 in H4. apply IHt3 in H5.
  rewrite H2. rewrite H4. rewrite H5. simpl. reflexivity.
  inversion HASTY; subst.
  apply IHt1 in H2. apply IHt2 in H4. apply IHt3 in H5.
  simpl.
  rewrite H2. rewrite H4. rewrite H5. simpl. reflexivity.
  inversion HASTY. simpl. reflexivity.
  simpl. inversion HASTY. simpl. inversion HASTY. apply IHt in H0. apply H0.
  inversion HASTY. simpl. inversion HASTY. apply IHt in H0. apply H0.
  simpl. inversion HASTY. apply IHt in H0. apply H0.
  simpl. inversion HASTY.
Qed.

(*-- Check --*)

Check (conj tycheck_ex1 tycheck_ex2 :
 (tycheck
    (tif (tiszero (tpred (tsucc (tsucc tzero)))) ttrue (tiszero (tsucc tzero))) 
    TBool 
  = true)
 /\
 (tycheck
    (tif (tiszero (tpred (tsucc (tsucc tzero)))) tzero (tiszero (tsucc tzero))) 
    TBool 
  = false)).

Check tycheck_correct1: forall t T
    (TYCHK: tycheck t T = true),
  |- t \in T.

Check tycheck_correct2: forall t T
    (HASTY: |- t \in T),
  tycheck t T = true.
