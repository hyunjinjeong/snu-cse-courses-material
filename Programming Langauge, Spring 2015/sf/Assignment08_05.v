Require Export Assignment08_04.

(* problem #05: 20 points *)

(** Write a function which compiles an [aexp] into a stack
    machine program. The effect of running the program should be the
    same as pushing the value of the expression on the stack. *)

Fixpoint s_compile (e : aexp) : list sinstr :=
  match e with
  | ANum n => [SPush n]
  | AId id => [SLoad id]
  | APlus e1 e2 => (s_compile e1) ++ (s_compile e2) ++ [SPlus]
  | AMinus e1 e2 => (s_compile e1) ++ (s_compile e2) ++ [SMinus]
  | AMult e1 e2 => (s_compile e1) ++ (s_compile e2) ++ [SMult]
  end.

(** After you've defined [s_compile], prove the following to test
    that it works. *)

Example s_compile1 :
    s_compile (AMinus (AId X) (AMult (ANum 2) (AId Y)))
  = [SLoad X; SPush 2; SLoad Y; SMult; SMinus].
Proof.
  reflexivity.
Qed.

(** **** Exercise: 3 stars, advanced (stack_compiler_correct)  *)
(** The task of this exercise is to prove the correctness of the
    compiler implemented in the previous exercise.  Remember that
    the specification left unspecified what to do when encountering an
    [SPlus], [SMinus], or [SMult] instruction if the stack contains
    less than two elements.  (In order to make your correctness proof
    easier you may find it useful to go back and change your
    implementation!)

    Prove the following theorem, stating that the [compile] function
    behaves correctly.  You will need to start by stating a more
    general lemma to get a usable induction hypothesis; the main
    theorem will then be a simple corollary of this lemma. *)

Lemma s_compile_sub1 : forall st p1 p2 stack,
  s_execute st stack (p1 ++ p2) = s_execute st (s_execute st stack p1) p2.
Proof.
  intros st p1.
  induction p1.
  intros.
  simpl.
  reflexivity.
  intros.
  simpl.
  destruct stack; destruct a; try (apply IHp1);
  destruct stack; try (apply IHp1).
Qed.
  

Lemma s_compile_sub0 : forall (e : aexp) (st : state) (stack: list nat),
  s_execute st stack (s_compile e) = aeval st e :: stack.
Proof.
  intros e st.
  induction e; try (intros; simpl; reflexivity);
  try (simpl; intros; rewrite s_compile_sub1; rewrite s_compile_sub1;
  rewrite IHe1; rewrite IHe2; reflexivity).
Qed.


Theorem s_compile_correct : forall (st : state) (e : aexp),
  s_execute st [] (s_compile e) = [ aeval st e ].
Proof.
  intros.
  rewrite s_compile_sub0.
  reflexivity.
Qed.

(*-- Check --*)
Check s_compile1 :
    s_compile (AMinus (AId X) (AMult (ANum 2) (AId Y)))
  = [SLoad X; SPush 2; SLoad Y; SMult; SMinus].

Check s_compile_correct : forall (st : state) (e : aexp),
  s_execute st [] (s_compile e) = [ aeval st e ].

