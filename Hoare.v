(** Exercise: 1 star, optional (valid_triples)
Which of the following Hoare triples are valid — i.e., the claimed relation between P, c, and Q is true?

1) {{True}} X ::= 5 {{X = 5}}
  VALID. El programa ejecuta siempre X igual a 5.
  Se cumple la postcondicion.

   2) {{X = 2}} X ::= X + 1 {{X = 3}}
  VALID. 

   3) {{True}} X ::= 5; Y ::= 0 {{X = 5}}
  VALID. La postcondicion se cumple.

   4) {{X = 2 /\ X = 3}} X ::= 5 {{X = 0}}
  NOT VALID. Al final del programa X sera 5, no 0.
  Postcondicion erronea.

   5) {{True}} SKIP {{False}}
   NOT VALID
   
   6) {{False}} SKIP {{True}}
   NOT VALID

   7) {{True}} WHILE True DO SKIP END {{False}}
   NOT VALID

   8) {{X = 0}}
      WHILE X == 0 DO X ::= X + 1 END
      {{X = 1}}
  VALID.
  X=0, se mete al bucle, la inrementa, y acaba el bucle pues X es 1.

   9) {{X = 1}}
      WHILE X <> 0 DO X ::= X + 1 END
      {{X = 100}}
  NOT VALID. Bucle infinito.
*)

(** Exercise: 2 starsM (hoare_asgn_examples) **)

(** "1.-" Translate these informal Hoare triples...

    1) {{ (X <= 5) [X |-> X + 1] }}
       X ::= X + 1
       {{ X <= 5 }}

    2) {{ (0 <= X /\ X <= 5) [X |-> 3] }}
       X ::= 3
       {{ 0 <= X /\ X <= 5 }}

   ...into formal statements (use the names [assn_sub_ex1] 
   and [assn_sub_ex2]) and use [hoare_asgn] to prove them. *)

Example assn_sub_ex1 :
  {{(fun st => st X <= 5) [X |-> (APlus (AId X) (ANum 1))]}}
  (X ::= (APlus (AId X) (ANum 1)))
  {{fun st => st X <= 5}}.
Proof.
  apply hoare_asgn.  Qed.

Example assn_sub_ex2 :
  {{(fun st => 0 <= st X /\ st X <= 5) [X |-> ANum 3]}}
  (X ::= ANum 3)
  {{fun st => 0 <= st X /\ st X <= 5}}.
Proof.
  apply hoare_asgn.  Qed.

(** Exercise: 3 stars, advanced (hoare_asgn_fwd) **)

(** 
   However, by using an auxiliary variable [m] to remember the 
    original value of [X] we can define a Hoare rule for assignment 
    that does, intuitively, "work forwards" rather than backwards.

       ------------------------------------------ (hoare_asgn_fwd)
       {{fun st => P st /\ st X = m}}
         X ::= a
       {{fun st => P st' /\ st X = aeval st' a }}
       (where st' = t_update st X m)

    Note that we use the original value of [X] to reconstruct the
    state [st'] before the assignment took place. Prove that this rule
    is correct (the first hypothesis is the functional extensionality
    axiom, which you will need at some point). Also note that this
    rule is more complicated than [hoare_asgn].
*)

Theorem eq_id_dec : forall id1 id2 : id, {id1 = id2} + {id1 <> id2}.
Proof.
   intros id1 id2.
   destruct id1 as [n1]. destruct id2 as [n2].
   destruct (eq_nat_dec n1 n2) as [Heq | Hneq].
   +
     left. rewrite Heq. reflexivity.
   +
     right. intros contra. inversion contra. apply Hneq. apply H0.
Defined.

Theorem hoare_asgn_fwd :
  (forall {X Y: Type} {f g : X -> Y},
     (forall (x: X), f x = g x) ->  f = g) ->
  forall m a P,
  {{fun st => P st /\ st X = m}}
    X ::= a
  {{fun st => P (t_update st X m) 
            /\ st X = aeval (t_update st X m) a }}.
Proof.
  intros functional_extensionality m a P.
  unfold hoare_triple. intros. destruct H0.
  inversion H; subst.
  assert (t_update (t_update st X (aeval st a)) X (st X) = st).
  apply functional_extensionality. intros. rewrite t_update_shadow.
  destruct (eq_id_dec X x). rewrite e. rewrite t_update_eq. reflexivity.
  rewrite t_update_neq. reflexivity. assumption.
  rewrite H1. split. assumption. rewrite t_update_eq. reflexivity.
Qed.


(** Exercise: 2 starsM (hoare_asgn_examples_2) **)

(** Translate these informal Hoare triples...

       {{ X + 1 <= 5 }}  X ::= X + 1  {{ X <= 5 }}
       {{ 0 <= 3 /\ 3 <= 5 }}  X ::= 3  {{ 0 <= X /\ X <= 5 }}

   ...into formal statements (name them [assn_sub_ex1'] and 
   [assn_sub_ex2']) and use [hoare_asgn] and [hoare_consequence_pre] 
   to prove them. *)

Example assn_sub_ex1' :
  {{ fun st => st X + 1 <= 5 }}
  ( X ::= (APlus (AId X) (ANum 1)) )     
  {{ fun st => st X <= 5 }}.
Proof.
  eapply hoare_consequence_pre.
  apply hoare_asgn.
  intros st H. unfold assn_sub. unfold t_update. simpl. 
  assumption.
Qed.

Example assn_sub_ex2' :
  {{ fun st => 0 <= 3 /\ 3 <= 5 }}
  ( X ::= ANum 3 )
  {{ fun st => 0 <= st X /\ st X <= 5 }}.
Proof.
  eapply hoare_consequence_pre.
  apply hoare_asgn.
  intros st H. unfold assn_sub, t_update. simpl.
  assumption.
Qed.


(** Exercise: 2 stars, recommended (hoare_asgn_example4) **)
(** Translate this "decorated program" into a formal proof:

                   {{ True }} ->>
                   {{ 1 = 1 }}
    X ::= 1;;
                   {{ X = 1 }} ->>
                   {{ X = 1 /\ 2 = 2 }}
    Y ::= 2
                   {{ X = 1 /\ Y = 2 }}
*)

Example hoare_asgn_example4 :
  {{fun st => True}} (X ::= (ANum 1);; Y ::= (ANum 2))
  {{fun st => st X = 1 /\ st Y = 2}}.
Proof.
  eapply hoare_seq.
  apply hoare_asgn.
  eapply hoare_consequence_pre.
  apply hoare_asgn.
  intros st H.
  unfold assn_sub, t_update. simpl. split; reflexivity.
Qed.


(** Exercise: 3 stars (swap_exercise)
Exercise: 3 starsM (hoarestate1)
**)


(** Exercise: 2 stars (if_minus_plus) **)

(** Prove the following hoare triple using [hoare_if]: *)

(* "Usaremos los siguientes lemas de coq" *)
(* Lemma le_plus_minus n m : n <= m -> m = n + (m - n). 
  Lemma beq_nat_true n m : (n =? m) = true -> n=m. 
  Además, usaremos los siguientes *)

Fixpoint ble_nat n m  :=
  match n, m  with
    | O, _ => true
    | S n', O => false
    | S n', S m' => ble_nat n' m'
  end.

Theorem ble_nat_true : forall n m,
  ble_nat n m = true -> n <= m.
Proof.
  Admitted.


Theorem if_minus_plus :
  {{fun st => True}}
  IFB (BLe (AId X) (AId Y))
    THEN (Z ::= AMinus (AId Y) (AId X))
    ELSE (Y ::= APlus (AId X) (AId Z))
  FI
  {{fun st => st Y = st X + st Z}}.
Proof.
  apply hoare_if.
  - eapply hoare_consequence_pre.
    apply hoare_asgn.
    unfold bassn, assn_sub, t_update, assert_implies.
    simpl. intros. destruct H. apply le_plus_minus.
    apply ble_nat_true in H0. assumption.
  - eapply hoare_consequence_pre.
    apply hoare_asgn.
    unfold bassn, assn_sub, t_update, assert_implies.
    simpl. intros. reflexivity.
Qed.



(** *** Exercise: One-sided conditionals *)

(** In this exercise we consider extending Imp with "one-sided
    conditionals" of the form [IF1 b THEN c FI]. Here [b] is a
    boolean expression, and [c] is a command. If [b] evaluates to
    [true], then command [c] is evaluated. If [b] evaluates to
    [false], then [IF1 b THEN c FI] does nothing.

    We recommend that you do this exercise before the ones that
    follow, as it should help solidify your understanding of the
    material. *)

(** The first step is to extend the syntax of commands and introduce
    the usual notations.  (We've done this for you.  We use a separate
    module to prevent polluting the global name space.) *)

Module If1.

Inductive com : Type :=
  | CSkip : com
  | CAss : id -> aexp -> com
  | CSeq : com -> com -> com
  | CIf : bexp -> com -> com -> com
  | CWhile : bexp -> com -> com
  | CIf1 : bexp -> com -> com.

Notation "'SKIP'" :=
  CSkip.
Notation "c1 ;; c2" :=
  (CSeq c1 c2) (at level 80, right associativity).
Notation "X '::=' a" :=
  (CAss X a) (at level 60).
Notation "'WHILE' b 'DO' c 'END'" :=
  (CWhile b c) (at level 80, right associativity).
Notation "'IFB' e1 'THEN' e2 'ELSE' e3 'FI'" :=
  (CIf e1 e2 e3) (at level 80, right associativity).
Notation "'IF1' b 'THEN' c 'FI'" :=
  (CIf1 b c) (at level 80, right associativity).

(** Next we need to extend the evaluation relation to accommodate
    [IF1] branches.  This is for you to do... What rule(s) need to be
    added to [ceval] to evaluate one-sided conditionals? *)

Reserved Notation "c1 '/' st '\\' st'" (at level 40, st at level 39).

Inductive ceval : com -> state -> state -> Prop :=
  | E_Skip : forall st : state, SKIP / st \\ st
  | E_Ass : forall (st : state) (a1 : aexp) (n : nat) (X : id),
            aeval st a1 = n -> (X ::= a1) / st \\ t_update st X n
  | E_Seq : forall (c1 c2 : com) (st st' st'' : state),
            c1 / st \\ st' -> c2 / st' \\ st'' -> (c1 ;; c2) / st \\ st''
  | E_IfTrue : forall (st st' : state) (b1 : bexp) (c1 c2 : com),
               beval st b1 = true ->
               c1 / st \\ st' -> (IFB b1 THEN c1 ELSE c2 FI) / st \\ st'
  | E_IfFalse : forall (st st' : state) (b1 : bexp) (c1 c2 : com),
                beval st b1 = false ->
                c2 / st \\ st' -> (IFB b1 THEN c1 ELSE c2 FI) / st \\ st'
  | E_WhileEnd : forall (b1 : bexp) (st : state) (c1 : com),
                 beval st b1 = false -> (WHILE b1 DO c1 END) / st \\ st
  | E_WhileLoop : forall (st st' st'' : state) (b1 : bexp) (c1 : com),
                  beval st b1 = true ->
                  c1 / st \\ st' ->
                  (WHILE b1 DO c1 END) / st' \\ st'' ->
                  (WHILE b1 DO c1 END) / st \\ st''

  | E_If1True : forall (st st' : state) (b : bexp) (c : com),
               beval st b = true ->
               c / st \\ st' -> (IF1 b THEN c FI) / st \\ st'

  | E_If1fALSE : forall (st st' : state) (b : bexp) (c : com),
               beval st b = false ->
               (IF1 b THEN c FI) / st \\ st


  where "c1 '/' st '\\' st'" := (ceval c1 st st').

(** Now we repeat (verbatim) the definition and notation of Hoare triples. *)

Definition hoare_triple (P:Assertion) (c:com) (Q:Assertion) : Prop :=
  forall st st',
       c / st \\ st'  ->
       P st  ->
       Q st'.

Notation "{{ P }}  c  {{ Q }}" := (hoare_triple P c Q)
                                  (at level 90, c at next level)
                                  : hoare_spec_scope.

(** Finally, we (i.e., you) need to state and prove a theorem,
    [hoare_if1], that expresses an appropriate Hoare logic proof rule
    for one-sided conditionals. Try to come up with a rule that is
    both sound and as precise as possible. *)

Theorem hoare_if1 : forall P Q b c,
  {{fun st => P st /\ bassn b st}} c {{Q}} ->
  {{fun st => P st /\ ~(bassn b st)}} SKIP {{Q}} ->
  {{P}} (IF1 b THEN c FI) {{Q}}.

Proof.
  intros P Q b c HTrue HFalse st st' HP HQ.
  inversion HP; subst.
  - apply (HTrue st st'). assumption.
    split. assumption. apply bexp_eval_true. assumption.
  - apply (HFalse st'). constructor.
    split. assumption. apply bexp_eval_false. assumption.
Qed.

(** For full credit, prove formally [hoare_if1_good] that your rule is
    precise enough to show the following valid Hoare triple:

  {{ X + Y = Z }}
  IF1 Y <> 0 THEN
    X ::= X + Y
  FI
  {{ X = Z }}
*)

(** Hint: Your proof of this triple may need to use the other proof
    rules also. Because we're working in a separate module, you'll
    need to copy here the rules you find necessary. *)

(* destruct term eqn:naming_intro_pattern
This behaves as destruct term but adds an equation between 
term and the value that term takes in each of the possible cases. 
The name of the equation is specified by naming_intro_pattern*)

Lemma hoare_if1_good :
  {{ fun st => st X + st Y = st Z }}
  IF1 BNot (BEq (AId Y) (ANum 0)) THEN
    X ::= APlus (AId X) (AId Y)
  FI
  {{ fun st => st X = st Z }}.
Proof. 
  eapply hoare_if1.  
  - intros st st' H [H1 H2]. inversion H; subst.
    unfold t_update. simpl. assumption.
  - intros st st' H H1. inversion H; subst. destruct H1.
  unfold bassn in H1. simpl in H1.
  destruct (beq_nat (st' Y) 0) eqn:eqy. apply beq_nat_true in eqy.
  omega. unfold not in H1. simpl in H1. apply False_ind. apply H1.
  reflexivity.
Qed.


End If1.


(* "EJERCICIO: REPEAT" *)
(** Exercise: 4 stars, advancedM (hoare_repeat) **)

Module RepeatExercise.

Inductive com : Type :=
  | CSkip : com
  | CAsgn : id -> aexp -> com
  | CSeq : com -> com -> com
  | CIf : bexp -> com -> com -> com
  | CWhile : bexp -> com -> com
  | CRepeat : com -> bexp -> com.

(** [REPEAT] behaves like [WHILE], except that the loop guard is
    checked _after_ each execution of the body, with the loop
    repeating as long as the guard stays _false_.  Because of this,
    the body will always execute at least once. *)

Notation "'SKIP'" :=
  CSkip.
Notation "c1 ;; c2" :=
  (CSeq c1 c2) (at level 80, right associativity).
Notation "X '::=' a" :=
  (CAsgn X a) (at level 60).
Notation "'WHILE' b 'DO' c 'END'" :=
  (CWhile b c) (at level 80, right associativity).
Notation "'IFB' e1 'THEN' e2 'ELSE' e3 'FI'" :=
  (CIf e1 e2 e3) (at level 80, right associativity).
Notation "'REPEAT' e1 'UNTIL' b2 'END'" :=
  (CRepeat e1 b2) (at level 80, right associativity).

(** Add new rules for [REPEAT] to [ceval] below.  You can use the rules
    for [WHILE] as a guide, but remember that the body of a [REPEAT]
    should always execute at least once, and that the loop ends when
    the guard becomes true.  Then update the [ceval_cases] tactic to
    handle these added cases.  *)

Inductive ceval : state -> com -> state -> Prop :=
  | E_Skip : forall st,
      ceval st SKIP st
  | E_Ass  : forall st a1 n X,
      aeval st a1 = n ->
      ceval st (X ::= a1) (t_update st X n)
  | E_Seq : forall c1 c2 st st' st'',
      ceval st c1 st' ->
      ceval st' c2 st'' ->
      ceval st (c1 ;; c2) st''
  | E_IfTrue : forall st st' b1 c1 c2,
      beval st b1 = true ->
      ceval st c1 st' ->
      ceval st (IFB b1 THEN c1 ELSE c2 FI) st'
  | E_IfFalse : forall st st' b1 c1 c2,
      beval st b1 = false ->
      ceval st c2 st' ->
      ceval st (IFB b1 THEN c1 ELSE c2 FI) st'
  | E_WhileEnd : forall b1 st c1,
      beval st b1 = false ->
      ceval st (WHILE b1 DO c1 END) st
  | E_WhileLoop : forall st st' st'' b1 c1,
      beval st b1 = true ->
      ceval st c1 st' ->
      ceval st' (WHILE b1 DO c1 END) st'' ->
      ceval st (WHILE b1 DO c1 END) st''
  | E_Repeat : forall b c st st' st'',
      ceval st c st' ->
      ceval st' (WHILE (BNot b) DO c END) st'' ->
      ceval st (REPEAT c UNTIL b END) st''.


(** A couple of definitions from above, copied here so they use the
    new [ceval]. *)

Notation "c1 '/' st '\\' st'" := (ceval st c1 st')
                                 (at level 40, st at level 39).

Definition hoare_triple (P:Assertion) (c:com) (Q:Assertion)
                        : Prop :=
  forall st st', (c / st \\ st') -> P st -> Q st'.

Notation "{{ P }}  c  {{ Q }}" :=
  (hoare_triple P c Q) (at level 90, c at next level).

(** To make sure you've got the evaluation rules for [REPEAT] right,
    prove that [ex1_repeat evaluates correctly. *)

Definition ex1_repeat :=
  REPEAT
    X ::= ANum 1;;
    Y ::= APlus (AId Y) (ANum 1)
  UNTIL (BEq (AId X) (ANum 1)) END.

Theorem ex1_repeat_works :
  ex1_repeat / empty_state \\
               t_update (t_update empty_state X 1) Y 1.
Proof.
  eapply E_Repeat.
  - eapply E_Seq; constructor; reflexivity.
  - apply E_WhileEnd. reflexivity. 
Qed.

(** Now state and prove a theorem, [hoare_repeat], that expresses an
    appropriate proof rule for [repeat] commands.  Use [hoare_while]
    as a model, and try to make your rule as precise as possible. *)

Lemma hoare_repeat : forall P Q R b c,
  {{ P }} c {{ Q }} ->
  {{ Q }} WHILE BNot b DO c END {{ R }} ->
  {{ P }} REPEAT c UNTIL b END {{ R }}.
Proof.
  intros.
  intros st st' H1 H2.
  inversion H1; subst.
  apply (H0 st'0 st'). assumption.
  apply (H st st'0); assumption.
Qed.

(** For full credit, make sure (informally) that your rule can be used
    to prove the following valid Hoare triple:

  {{ X > 0 }}
  REPEAT
    Y ::= X;;
    X ::= X - 1
  UNTIL X = 0 END
  {{ X = 0 /\ Y > 0 }}
*)

End RepeatExercise.
