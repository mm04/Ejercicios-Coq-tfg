(** Exercise: (optimize_0plus_b)
Since the optimize_0plus transformation doesn't change the value of aexps, 
we should be able to apply it to all the aexps that appear in a bexp without changing the bexp's value. 
Write a function which performs that transformation on bexps, and prove it is sound. 
Use the tacticals we've just seen to make the proof as elegant as possible. **)

Fixpoint optimize_0plus_b (b : bexp) : bexp :=
  match b with
  | BTrue =>
      BTrue
  | BFalse =>
      BFalse
  | BEq e1 e2 =>
      BEq (optimize_0plus e1) (optimize_0plus e2)
  | BLe e1 e2 =>
      BLe (optimize_0plus e1) (optimize_0plus e2)
  | BNot b =>
      BNot b
  | BAnd b1 b2 =>
      BAnd b1 b2
  end.

Theorem optimize_0plus_b_sound : ∀b,
  beval (optimize_0plus_b b) = beval b.
Proof.
  intros. induction b; simpl;
  try (rewrite optimize_0plus_sound);
  try (rewrite optimize_0plus_sound);
  reflexivity.
Qed.

(** Exercise: (bevalR) **)
(* Write a relation [bevalR] in the same style as
    [aevalR], and prove that it is equivalent to [beval].*)
    
Reserved Notation "e '//' n" (at level 50, left associativity).

Inductive bevalR: bexp -> bool -> Prop :=
  | E_BTrue : BTrue // true
  | E_BFalse : BFalse // false
  | E_BEq : forall (e1 e2: aexp) (n1 n2 : nat),
    e1 \\ n1 ->
    e2 \\ n2 ->
    BEq e1 e2 // (beq_nat n1 n2)
  | E_BLe : forall (e1 e2: aexp) (n1 n2 : nat),
    e1 \\ n1 ->
    e2 \\ n2 ->
    BLe e1 e2 // (ble_nat n1 n2)
  | E_BNot : forall (e: bexp) (b:bool), 
    BNot e // negb b
  | E_BAnd : forall (e1 e2: bexp) (b1 b2: bool), 
    BAnd e1 e2 // b1 && b2

   where "e '//' n" := (bevalR e n) : type_scope.

Reserved Notation "e '\\' n" (at level 50, left associativity).

(** **** Exercise: (ceval_example2)  *)
Example ceval_example2:
    (X ::= ANum 0;; Y ::= ANum 1;; Z ::= ANum 2) / empty_state \\
    (t_update (t_update (t_update empty_state X 0) Y 1) Z 2).
Proof.
  apply E_Seq with (t_update empty_state X 0).
  - apply E_Ass. reflexivity.
  - apply E_Seq with (t_update (t_update empty_state X 0) Y 1);
    (apply E_Ass; reflexivity).
Qed.


(** **** Exercise: (pup_to_n)  *)
(** Write an Imp program that sums the numbers from [1] to
   [X] (inclusive: [1 + 2 + ... + X]) in the variable [Y].
   Prove that this program executes as intended for [X] = [2]
   (the latter is trickier than you might expect). *)

Definition pup_to_n : com :=
  Y ::= ANum 0 ;;
  WHILE BNot (BEq (AId X) (ANum 0)) DO
  Y ::= APlus (AId Y) (AId X) ;;
  X ::= AMinus (AId X) (ANum 1)
  END.

Theorem pup_to_2_ceval :
  pup_to_n / (t_update empty_state X 2) \\
    t_update (t_update (t_update (t_update (t_update (t_update empty_state
      X 2) Y 0) Y 2) X 1) Y 3) X 0.
Proof.
  apply E_Seq with (t_update (t_update empty_state X 2) Y 0) .
  - apply E_Ass. reflexivity.
  - apply E_WhileLoop with (t_update (t_update (t_update (t_update empty_state X 2) Y 0) Y 2) X 1).
    + reflexivity.
    + apply E_Seq with (t_update (t_update (t_update empty_state X 2) Y 0) Y 2);
      (apply E_Ass; reflexivity).
    + apply E_WhileLoop with (t_update (t_update (t_update (t_update (t_update (t_update empty_state X 2) Y 0) Y 2) X 1) Y 3) X 0).
      * reflexivity.
      * apply E_Seq with (t_update (t_update (t_update (t_update (t_update empty_state X 2) Y 0) Y 2) X 1) Y 3);
        (apply E_Ass; reflexivity).
      * apply E_WhileEnd. reflexivity.
Qed.

(** **** Exercise: (loop_never_stops)  *)
Theorem loop_never_stops : forall st st',
  ~(loop / st \\ st').
Proof.
  intros st st' contra. unfold loop in contra.
  remember (WHILE BTrue DO SKIP END) as loopdef
           eqn:Heqloopdef.

  (** Proceed by induction on the assumed derivation showing that
      [loopdef] terminates.  Most of the cases are immediately
     contradictory (and so can be solved in one step with inversion).*)
  induction contra; inversion Heqloopdef; subst.
  simpl in H. inversion H. 
  apply IHcontra2. reflexivity.
Qed.

(** **** Exercise: (no_whilesR)  *)
(** Consider the definition of the [no_whiles] boolean predicate below: *)

Fixpoint no_whiles (c : com) : bool :=
  match c with
  | SKIP =>
      true
  | _ ::= _ =>
      true
  | c1 ;; c2 =>
      andb (no_whiles c1) (no_whiles c2)
  | IFB _ THEN ct ELSE cf FI =>
      andb (no_whiles ct) (no_whiles cf)
  | WHILE _ DO _ END  =>
      false
  end.

(** This predicate yields [true] just on programs that have no while
    loops.  Using [Inductive], write a property [no_whilesR] such that
    [no_whilesR c] is provable exactly when [c] is a program with no
    while loops.  Then prove its equivalence with [no_whiles]. *)

Inductive no_whilesR: com -> Prop :=
| nowhile_skip : no_whilesR SKIP
| nowhile_ass : forall id val, 
    no_whilesR (id ::= val)
| nowhile_seq : forall c1 c2, 
    no_whilesR c1 ->
    no_whilesR c2 ->
    no_whilesR (c1 ;; c2)
| nowhile_if : forall b ct cf, 
    no_whilesR ct ->
    no_whilesR cf ->
    no_whilesR (IFB b THEN ct ELSE cf FI).

Theorem no_whiles_eqv:
   forall c, no_whiles c = true <-> no_whilesR c.
Proof.
  split.
  - intros H. induction c; simpl in H;
          try(apply andb_true_iff in H; destruct H);
          try(constructor);
          try (apply IHc1);
          try (apply IHc2); try(assumption).
          inversion H.
  - intros. induction H; try (reflexivity);
    simpl; rewrite IHno_whilesR1; rewrite IHno_whilesR2;
    reflexivity.
Qed.

(* ################################################################# *)
(** * Additional Exercises *)

(** **** Exercise: (stack_compiler)  *)
(** HP Calculators, programming languages like Forth and Postscript,
    and abstract machines like the Java Virtual Machine all evaluate
    arithmetic expressions using a stack. For instance, the expression

      (2*3)+(3*(4-2))

   would be entered as

      2 3 * 3 4 2 - * +

   and evaluated like this (where we show the program being evaluated 
   on the right and the contents of the stack on the left):

      []            |    2 3 * 3 4 2 - * +
      [2]           |    3 * 3 4 2 - * +
      [3, 2]        |    * 3 4 2 - * +
      [6]           |    3 4 2 - * +
      [3, 6]        |    4 2 - * +
      [4, 3, 6]     |    2 - * +
      [2, 4, 3, 6]  |    - * +
      [2, 3, 6]     |    * +
      [6, 6]        |    +
      [12]          |

  The task of this exercise is to write a small compiler that
  translates [aexp]s into stack machine instructions.

  The instruction set for our stack language will consist of the
  following instructions:
     - [SPush n]: Push the number [n] on the stack.
     - [SLoad x]: Load the identifier [x] from the store and push it
                  on the stack
     - [SPlus]:   Pop the two top numbers from the stack, add them, and
                  push the result onto the stack.
     - [SMinus]:  Similar, but subtract.
     - [SMult]:   Similar, but multiply. *)

Inductive sinstr : Type :=
| SPush : nat -> sinstr
| SLoad : id -> sinstr
| SPlus : sinstr
| SMinus : sinstr
| SMult : sinstr.

(** Write a function to evaluate programs in the stack language. It
    should take as input a state, a stack represented as a list of
    numbers (top stack item is the head of the list), and a program
    represented as a list of instructions, and it should return the
    stack after executing the program.  Test your function on the
    examples below.

    Note that the specification leaves unspecified what to do when
    encountering an [SPlus], [SMinus], or [SMult] instruction if the
    stack contains less than two elements.  In a sense, it is
    immaterial what we do, since our compiler will never emit such a
    malformed program. *)

Fixpoint s_execute (st : state) (stack : list nat)
                   (prog : list sinstr)
                 : list nat :=
 match prog with
   | [] => stack
   | first_c :: commands => match first_c with
                           | SPush n => s_execute st (n :: stack) commands (* lo añadimos a la lista pila *)
                           | SLoad i => s_execute st (st i :: stack) commands
                           | SPlus => match stack with
                                       | f :: s :: t => s_execute st ((f+s) :: t) commands
                                       | _ => s_execute st stack commands
                                      end
                           | SMinus => match stack with
                                        | f :: s :: t => s_execute st ((s - f) :: t) commands
                                        | _ => s_execute st stack commands
                                       end
                           | SMult => match stack with
                                       | f :: s :: t => s_execute st ((s * f) :: t) commands
                                       | _ => s_execute st stack commands
                                      end
                           end
  end.


Example s_execute1 :
     s_execute empty_state []
       [SPush 5; SPush 3; SPush 1; SMinus]
   = [2; 5].
Proof. reflexivity. Qed.

Example s_execute2 :
     s_execute (t_update empty_state X 3) [3;4]
       [SPush 4; SLoad X; SMult; SPlus]
   = [15; 4].
Proof. reflexivity. Qed.

(** Next, write a function that compiles an [aexp] into a stack
    machine program. The effect of running the program should be the
    same as pushing the value of the expression on the stack. *)

Fixpoint s_compile (e : aexp) : list sinstr :=
  match e with
    | ANum n1 => [SPush n1]
    | AId i => [SLoad i]
    | APlus e1 e2 => (s_compile e1) ++ (s_compile e2) ++ [SPlus]
    | AMinus e1 e2 => (s_compile e1) ++ (s_compile e2) ++ [SMinus]
    | AMult e1 e2 => (s_compile e1) ++ (s_compile e2) ++ [SMult]

  end.

(** After you've defined [s_compile], prove the following to test
    that it works. *)

Example s_compile1 :
    s_compile (AMinus (AId X) (AMult (ANum 2) (AId Y)))
  = [SLoad X; SPush 2; SLoad Y; SMult; SMinus].
Proof. reflexivity. Qed.
