(** **** Exercise: (substi)  *)
(** The definition that we gave above uses Coq's [Fixpoint] facility
    to define substitution as a _function_.  Suppose, instead, we
    wanted to define substitution as an inductive _relation_ [substi].
    We've begun the definition by providing the [Inductive] header and
    one of the constructors; your job is to fill in the rest of the
    constructors and prove that the relation you've defined coincides
    with the function given above. *)

Inductive substi (s:tm) (x:id) : tm -> tm -> Prop :=
  | s_var1 :
      substi s x (tvar x) s
  | s_var2 :
      forall y,
        x <> y ->
        substi s x (tvar y) (tvar y)
  | s_abs1 :
      forall m T,
        substi s x (tabs x T m) (tabs x T m)
  | s_abs2 :
      forall m m' T y,
        x <> y ->
        substi s x m m' ->
        substi s x (tabs y T m) (tabs y T m')
  | s_app :
      forall t1 t2 t1' t2',
        substi s x t1 t1' ->
        substi s x t2 t2' ->
        substi s x (tapp t1 t2) (tapp t1' t2')
  | s_true :
      substi s x ttrue ttrue
  | s_false :
      substi s x tfalse tfalse
  | s_if :
      forall t1 t2 t3 t1' t2' t3',
        substi s x t1 t1' ->
        substi s x t2 t2' ->
        substi s x t3 t3' ->
        substi s x (tif t1 t2 t3) (tif t1' t2' t3').


(** **** Exercise: (step_example3)  *)
(** Try to do this one both with and without [normalize]. *)

Lemma step_example5 :
       (tapp (tapp idBBBB idBB) idB)
  ==>* idB.
Proof.
  eapply multi_step. apply ST_App1. auto.
  eapply multi_step.  apply ST_AppAbs. auto.
  eapply multi_refl.
Qed.

Lemma step_example5_with_normalize :
       (tapp (tapp idBBBB idBB) idB)
  ==>* idB.
Proof.
  normalize. Qed.

(** **** Exercise: (typing_example_2_full)  *)
(** Prove the same result without using [auto], [eauto], or
    [eapply] (or [...]). *)

Example typing_example_2_full :
  empty |-
    (tabs x TBool
       (tabs y (TArrow TBool TBool)
          (tapp (tvar y) (tapp (tvar y) (tvar x))))) \in
    (TArrow TBool (TArrow (TArrow TBool TBool) TBool)).
Proof.
  apply T_Abs. apply T_Abs.
  apply T_App with (T11 := TBool). 
  apply T_Var. reflexivity.
  apply T_App with (T11 := TBool);
  apply T_Var; reflexivity.
Qed.

(** **** Exercise: (typing_example_3)  *)
(** Formally prove the following typing derivation holds: *)
(** 
       empty |- \x:Bool->B. \y:Bool->Bool. \z:Bool.
                   y (x z)
             \in T.
*)

Example typing_example_3 :
  exists T,
    empty |-
      (tabs x (TArrow TBool TBool)
         (tabs y (TArrow TBool TBool)
            (tabs z TBool
               (tapp (tvar y) (tapp (tvar x) (tvar z)))))) \in
      T.
Proof with auto.
  eexists. apply T_Abs.
  apply T_Abs. apply T_Abs.
  apply T_App with (T11 := TBool).
  apply T_Var. reflexivity.
  apply T_App with (T11 := TBool); apply T_Var; reflexivity.
Qed.

(** **** Exercise: (typable_empty__closed)  *)
Corollary typable_empty__closed : forall t T,
    empty |- t \in T  ->
    closed t.
Proof.
  intros t T H. unfold closed, not. intros.
  apply free_in_context with (T := T) (Gamma := empty) in H0.
  inversion H0; subst. inversion H1. assumption.
Qed.
