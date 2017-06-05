(** Exercise: 2 starsM (if_minus_plus_reloaded) **)

(** Fill in valid decorations for the following program:

   {{ True }}
  IFB X <= Y THEN
      {{ True /\ X <= Y }} ->>
      {{ Y = X + (Y - X) }}
    Z ::= Y - X
      {{ Y = X + Z }}
  ELSE
      {{ True /\ ~(X <= Y)}} ->>
      {{ (X + Z) = X + Z }}
    Y ::= X + Z
      {{ Y = X + Z }}
  FI
    {{ Y = X + Z }}
*)

(* 1 -> 
{{ True /\ X <= Y }} ->>
      {{ Y = X + (Y - X) }}
Si X <= Y entonces Y-X > 0, e Y-X+X = Y

2 ->
{{ True /\ ~(X <= Y)}} ->>
      {{ (X + Z) = X + Z }}
Se sigue directamente.
*)


(** Exercise: 2 starsM (slow_assignment) **)

(** (slow_assignment)  *)
(** A roundabout way of assigning a number currently stored in [X] to
    the variable [Y] is to start [Y] at [0], then decrement [X] until
    it hits [0], incrementing [Y] at each step. Here is a program that
    implements this idea:

        {{ X = m }}
      Y ::= 0;;
      WHILE X <> 0 DO
        X ::= X - 1;;
        Y ::= Y + 1
      END
        {{ Y = m }}

    Write an informal decorated program showing that this procedure 
    is correct. *)

(* FILL IN HERE *)
(* ESQUELETO *)
(**
      {{ X = m }} ->>
      {{ I [Y |-> 0] }}
      Y ::= 0;
      WHILE X <> 0 DO
          {{ I /\ X <> 0 }} ->>
          {{ I [Y |-> Y + 1] [X |-> X - 1] }}
        X ::= X - 1;;
          {{ I [Y |-> Y + 1]
        Y ::= Y + 1
          {{ I }}
      END
        {{ I /\ ~(X <> 0) }}
        {{ Y = m }}
**)
(* SOLUCION: Y+X=m *)
(**
      {{ X = m }} 
      Y :: = 0
      {{ X = m /\ Y = 0 }} ->>
      {{ X + Y = m }}
      WHILE X <> 0 DO
          {{ Y + X = m /\ X <> 0 }} ->>
          {{ (Y + 1) + (X - 1) = m  }}
        X ::= X - 1;;
          {{ (Y + 1) + X = m }}
        Y ::= Y + 1
          {{ Y + X = m }}
      END
        {{ Y + X = m /\ ~ (X <> 0) }}
        {{ Y = m }}
**)


(** Exercise: 3 stars, optional (add_slowly_decoration) **)

(** ** Exercise: Slow Addition *)

(** **** Exercise: 3 stars, optional (add_slowly_decoration)  *)
(** The following program adds the variable X into the variable Z
    by repeatedly decrementing X and incrementing Z.

      WHILE X <> 0 DO
         Z ::= Z + 1;;
         X ::= X - 1
      END

    Following the pattern of the [subtract_slowly] example above, pick
    a precondition and postcondition that give an appropriate
    specification of [add_slowly]; then (informally) decorate the
    program accordingly. *)

(* FILL IN HERE *)
(**
      {{ X = m /\ Z = n }}
      WHILE X <> 0 DO
         Z ::= Z + 1;;
         X ::= X - 1
      END
      {{ Z = n + m }} **)

(* ESQUELETO: *)
(**
      {{ X = m /\ Z = n }} ->>
      {{ I }}
      WHILE X <> 0 DO
          {{ I /\ X <> 0 }}
          {{ I [X |-> X-1] [Z |-> Z +1 ] }}
         Z ::= Z + 1;;
          {{ I [X |-> X-1] }}
         X ::= X - 1
          {{ I }}
      END
      {{ I /\ ~ (X <> 0) }} ->>
      {{ Z = n + m }} **)
      
(* SOLUCION: I = Z + X = n + m *)
(**
      {{ X = m /\ Z = n }} ->>
      {{ Z + X = n + m }}
      WHILE X <> 0 DO
          {{ Z + X = n + m /\ X <> 0 }} ->>
          {{ (Z + 1) + (X - 1) = n + m }}
         Z ::= Z + 1;;
          {{ Z + (X - 1) = n + m }}
         X ::= X - 1
          {{ Z + X = n + m }}
      END
      {{ Z + X = n + m /\ ~ (X <> 0) }} ->>
      {{ Z = n + m }} 
**)



(** Exercise: 3 stars, optional (add_slowly_decoration) **)

(** ** Exercise: Slow Addition *)

(** **** Exercise: 3 stars, optional (add_slowly_decoration)  *)
(** The following program adds the variable X into the variable Z
    by repeatedly decrementing X and incrementing Z.

      WHILE X <> 0 DO
         Z ::= Z + 1;;
         X ::= X - 1
      END

    Following the pattern of the [subtract_slowly] example above, pick
    a precondition and postcondition that give an appropriate
    specification of [add_slowly]; then (informally) decorate the
    program accordingly. *)

(* FILL IN HERE *)
(**
      {{ X = m /\ Z = n }}
      WHILE X <> 0 DO
         Z ::= Z + 1;;
         X ::= X - 1
      END
      {{ Z = n + m }} **)

(* ESQUELETO: *)
(**
      {{ X = m /\ Z = n }} ->>
      {{ I }}
      WHILE X <> 0 DO
          {{ I /\ X <> 0 }}
          {{ I [X |-> X-1] [Z |-> Z +1 ] }}
         Z ::= Z + 1;;
          {{ I [X |-> X-1] }}
         X ::= X - 1
          {{ I }}
      END
      {{ I /\ ~ (X <> 0) }} ->>
      {{ Z = n + m }} **)
      
(* SOLUCION: I = Z + X = n + m *)
(**
      {{ X = m /\ Z = n }} ->>
      {{ Z + X = n + m }}
      WHILE X <> 0 DO
          {{ Z + X = n + m /\ X <> 0 }} ->>
          {{ (Z + 1) + (X - 1) = n + m }}
         Z ::= Z + 1;;
          {{ Z + (X - 1) = n + m }}
         X ::= X - 1
          {{ Z + X = n + m }}
      END
      {{ Z + X = n + m /\ ~ (X <> 0) }} ->>
      {{ Z = n + m }} 
**)


(** Exercise: 3 stars, optional (parity_formal) **)

(** Translate this proof to Coq. Refer to the reduce-to-zero example
    for ideas. You may find the following two lemmas useful: *)

Lemma parity_ge_2 : forall x,
  2 <= x ->
  parity (x - 2) = parity x.
Proof.
  induction x; intro. reflexivity.
  destruct x. inversion H. inversion H1.
  simpl. rewrite <- minus_n_O. reflexivity.
Qed.

Lemma parity_lt_2 : forall x,
  ~ 2 <= x ->
  parity (x) = x.
Proof.
  intros. induction x. reflexivity. destruct x. reflexivity.
    exfalso. apply H. omega.
Qed.

Theorem parity_correct : forall m,
    {{ fun st => st X = m }}
  WHILE BLe (ANum 2) (AId X) DO
    X ::= AMinus (AId X) (ANum 2)
  END
    {{ fun st => st X = parity m }}.
Proof.
  intros.
  eapply hoare_consequence_pre with (fun st => parity (st X) = parity m).
  eapply hoare_consequence_post.
  apply hoare_while.
  - eapply hoare_consequence_pre.
  apply hoare_asgn.
  intros st H. unfold assn_sub, t_update. simpl.
  inversion H. rewrite -> parity_ge_2. 
  assumption. 
  unfold bassn in H1.
  apply ble_nat_true in H1. 
  assumption.
  - intros st [H1 H2]. 
    rewrite <- H1. symmetry. apply parity_lt_2.
    unfold not. intros. unfold bassn in H2; simpl in H2.
    destruct (st X). omega. destruct n. omega. apply H2. reflexivity.
  - intros st H. rewrite H; reflexivity.
Qed.



(** Exercise: 3 starsM (factorial) **)
(** Recall that [n!] denotes the factorial of [n] (i.e., [n! =
    1*2*...*n]).  Here is an Imp program that calculates the factorial
    of the number initially stored in the variable [X] and puts it in
    the variable [Y]:

    {{ X = m }}
  Y ::= 1 ;;
  WHILE X <> 0
  DO
     Y ::= Y * X ;;
     X ::= X - 1
  END
    {{ Y = m! }}


    Fill in the blanks in following decorated program:

    {{ X = m }} ->>
    {{ X! = m! }}
  Y ::= 1;;
    {{ X! * Y = m! }}
  WHILE X <> 0 DO   
       {{ X! * Y = m! /\ X <> 0 }} ->>
       {{ (X - 1)! * Y*X = m! }}                                     }}
     Y ::= Y * X;;
       {{ (X - 1)! * Y = m! }}
     X ::= X - 1
       {{ X! * Y = m! }}                                }}
  END
    {{ X! * Y = m! ~ (X <> 0) }} ->>
    {{ Y = m! }}
*)




(** Exercise: 3 starsM (Min_Hoare) **)
(* ================================================================= *)
(** ** Exercise: Min *)

(** **** Exercise: 3 stars (Min_Hoare)  *)
(** Fill in valid decorations for the following program.
  For the [=>] steps in your annotations, you may rely (silently) 
  on the following facts about min **)

  Lemma lemma1 : forall x y,
    (x=0 \/ y=0) -> min x y = 0.
  Lemma lemma2 : forall x y,
    min (x-1) (y-1) = (min x y) - 1.

(**
  plus standard high-school algebra, as always.


  {{ True }} ->>
  {{ min (a,b) = min (a,b) }}
  X ::= a;;
  {{ min (X,b) = min (a,b) }}
  Y ::= b;;
  {{ 0 + min (X,Y) = min (a,b) }}
  Z ::= 0;;
  {{ Z + min (X,Y) = min (a,b) }}
  WHILE (X <> 0 /\ Y <> 0) DO
      {{ Z + min (X,Y) = min (a,b)
            /\ X <> 0 /\ Y <> 0 }} ->>
      {{ Z+1 + min (X-1,Y-1) = min (a,b) }}
    X := X - 1;;
      {{ Z+1 + min (X,Y-1) = min (a,b) }}
    Y := Y - 1;;
      {{ Z+1 + min (X,Y) = min (a,b) }}
    Z := Z + 1
      {{ Z + min (X,Y) = min (a,b) }}
  END
    {{ Z + min (X,Y) = min (a,b) 
              /\ (X = 0 \/ Y = 0) }} ->>
    {{ Z = min a b }}
*)

(* INVARIANTE: Z + min (X,Y) = min (a,b) *)

(* A lo largo del bucle, siempre se cumple
que al sumar Z conel mínimo de X e Y este valor
coincide con el mínimo de los valores iniciales
de X e Y (en este caso a y b).
Por eso probamos esta opcion *)




(** Exercise: 3 starsM (two_loops) **)
(** Here is a very inefficient way of adding 3 numbers:

  X ::= 0;;
  Y ::= 0;;
  Z ::= c;;
  WHILE X <> a DO
    X ::= X + 1;;
    Z ::= Z + 1
  END;;
  WHILE Y <> b DO
    Y ::= Y + 1;;
    Z ::= Z + 1
  END


    Show that it does what it should by filling in the blanks in the
    following decorated program.


    {{ True }} ->>
    {{ c = c }}
  X ::= 0;;
    {{ c = X + c }}
  Y ::= 0;;
    {{ c = X + Y + c }}
  Z ::= c;;
    {{ Z = X + Y + c }}
  WHILE X <> a DO
      {{ Z = X + Y + c /\ X <> a }} ->>
      {{ (Z+1) = (X+1) + Y + c }}
    X ::= X + 1;;
      {{ (Z+1) = X + Y + c }}
    Z ::= Z + 1
      {{ Z = X + Y + c }}
  END;;
    {{ Z = X + Y + c /\ X = a }} ->>
    {{ Z = a + Y + c }}
  WHILE Y <> b DO
      {{ Z = a + Y + c /\ Y <> b }} ->>
      {{ Z+1 = a + Y+1 + c }}
    Y ::= Y + 1;;
      {{ Z+1 = a + Y + c }}
    Z ::= Z + 1
      {{ Z = a + Y + c }}
  END
    {{ Z = a + Y + c /\ Y = b }} ->>
    {{ Z = a + b + c }}
*)

(** [] *)

(* INVARIANTE 1: Z = X + Y + c *)
(* INVARIANTE 2: Z = a + Y + c *)

(* Al final del primer bucle X vale a,
luego permanece invariante en el segundo. 
Al final del segundo Y valdrá b,
pero Y y Z cambian. 
La c siempre permanece inalterada *)




(** "EJERCICIO: " Power Series *)
(** Exercise: 4 stars, optional (dpow2_down) **)
(** Here is a program that computes the series:
    [1 + 2 + 2^2 + ... + 2^m = 2^(m+1) - 1]

  X ::= 0;;
  Y ::= 1;;
  Z ::= 1;;
  WHILE X <> m DO
    Z ::= 2 * Z;;
    Y ::= Y + Z;;
    X ::= X + 1
  END

    Write a decorated program for this. *)

(* FILL IN HERE *)

(* Haciendo cuentas en papel con ejemplos
llegamos a la posibilidad del siguiente
invariante:
  Y = 2 * Z - 1 /\ Z = 2 ^ X 
*)
(*
    {{ True }} ->>
    {{ 1 = 1 /\ 1 = 2^0 }}
  X ::= 0;;
    {{ 1 = 1 /\ 1 = 2 ^ X  }}
  Y ::= 1;;
    {{ Y = 2 - 1 /\ 1 = 2 ^ X  }}
  Z ::= 1;;
    {{ Y = 2 * Z - 1 /\ Z = 2 ^ X  }}
  WHILE X <> m DO
      {{ Y = 2 * Z - 1 /\ Z = 2 ^ X
               /\ X <> m }} ->>
      {{ Y + 2 * Z = 2 * 2 * Z - 1 
           /\ 2 * Z = 2 ^ (X + 1) }}
    Z ::= 2 * Z ;;
      {{ Y + Z = 2 * Z - 1 
           /\ Z = 2 ^ (X + 1) }}
    Y ::= Y + Z;;
      {{ Y = 2 * Z - 1 /\ Z = 2 ^ (X + 1) }}
    X ::= X + 1
      {{ Y = 2 * Z - 1 /\ Z = 2 ^ X }}
  END
    {{ Y = 2 * Z - 1 /\ Z = 2 ^ X
           /\ X = m }} ->>
    {{ Y = 2 * Z - 1 /\ Z = 2 ^ m }}
*)

(* Efectivamente, y es la suma de las potencias
de 2 y, además, en la posconticion
se cumple que Y = 2*(m+1)-1.
Por lo tanto, este invariante es válido
(comprobando que, además,
se cumplen todas las implicaciones ->> *)


(** Exercise: 1 star, optional (wp) **)

(** "EJERCICIO: " **)
(** What are the weakest preconditions of the following commands
   for the following postconditions?

  1) {{ ? }}  SKIP  {{ X = 5 }}
      X = 5

  2) {{ ? }}  X ::= Y + Z {{ X = 5 }}
      Y + Z = 5

  3) {{ ? }}  X ::= Y  {{ X = Y }}
      True

  4) {{ ? }}
     IFB X == 0 THEN Y ::= Z + 1 ELSE Y ::= W + 2 FI
     {{ Y = 5 }}
      (X = 0 /\ Z = 4) \/ (X <> 0 /\ W = 3)

  5) {{ ? }}
     X ::= 5
     {{ X = 0 }}
      False

  6) {{ ? }}
     WHILE True DO X ::= 0 END
     {{ X = 0 }}
      True
*)




(** Exercise: 3 stars, advanced, optional (is_wp_formal) **)
(** Prove formally, using the definition of [hoare_triple], that [Y <= 4]
   is indeed the weakest precondition of [X ::= Y + 1] with respect to
   postcondition [X <= 5]. *)

Theorem is_wp_example :
  is_wp (fun st => st Y <= 4)
    (X ::= APlus (AId Y) (ANum 1)) (fun st => st X <= 5).
Proof.
  unfold is_wp. split.
  - eapply hoare_consequence_pre.
    apply hoare_asgn. intros st H.
    unfold assn_sub, t_update. simpl.
    omega.
  - intros P' H. 
    unfold assert_implies. intros st HP'.
    unfold hoare_triple in H.
    apply H with 
      (st' := t_update st X (st Y + 1)) in HP'.
    + unfold t_update in HP'. simpl in HP'. 
      omega.
    + constructor. simpl. reflexivity.
Qed.
    
    
    
(** Exercise: 2 stars, advanced, optional (hoare_asgn_weakest) **)
(** Show that the precondition in the rule [hoare_asgn] is in fact the
    weakest precondition. *)

Theorem hoare_asgn_weakest : forall Q X a,
  is_wp (Q [X |-> a]) (X ::= a) Q.
Proof.
  intros Q X a. 
  unfold is_wp. split.
  - apply hoare_asgn.
  - intros P' H. unfold assert_implies.
    intros st HP'.
    unfold hoare_triple in H.
    apply H with 
      (st' := t_update st X (aeval st a)) in HP'.
    + apply HP'.
    + constructor. reflexivity.
Qed.



(** Exercise: 3 stars, advanced (slow_assignment_dec) **)
(** In the [slow_assignment] exercise above, we saw a roundabout way
    of assigning a number currently stored in [X] to the variable [Y]:
    start [Y] at [0], then decrement [X] until it hits [0],
    incrementing [Y] at each step.  Write a formal version of this
    decorated program and prove it correct. *)

(**
      {{ X = m }} 
      Y :: = 0
      {{ X = m /\ Y = 0 }} ->>
      {{ X + Y = m }}
      WHILE X <> 0 DO
          {{ Y + X = m /\ X <> 0 }} ->>
          {{ (Y + 1) + (X - 1) = m  }}
        X ::= X - 1;;
          {{ (Y + 1) + X = m }}
        Y ::= Y + 1
          {{ Y + X = m }}
      END
        {{ Y + X = m /\ ~ (X <> 0) }}
        {{ Y = m }}
**)

Example slow_assignment_dec (m:nat) : dcom := (
    {{ fun st => st X = m }}
  Y ::= ANum 0
    {{ fun st => st X = m  /\ st Y = 0}} ->>
    {{ fun st => st X + st Y = m }} ;;
  WHILE BNot (BEq (AId X) (ANum 0))
  DO {{ fun st => st Y + st X = m /\ st X <> 0 }} ->>
     {{ fun st => (st Y + 1) + (st X - 1) = m }}
    X ::= AMinus (AId X) (ANum 1)
     {{ fun st => (st Y + 1) + st X = m }} ;;
    Y ::= APlus (AId Y) (ANum 1)
     {{ fun st => st Y + st X = m }}
  END
    {{ fun st => st Y + st X = m /\ st X = 0 }} ->>
    {{ fun st => st Y = m }}
) % dcom.

Theorem slow_assignment_dec_correct : forall m,
  dec_correct (slow_assignment_dec m).
Proof.
  intros m. verify. Qed.

