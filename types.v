(** **** Exercise: (some_term_is_stuck)  *)
Example some_term_is_stuck :
  exists t, stuck t.
Proof.
  exists (tsucc ttrue). unfold stuck. split.
  - unfold step_normal_form, not. intros. inversion H.
    inversion H0. inversion H2.
  - unfold not, value. intros [A | B].
    inversion A. inversion B. inversion H0.
Qed.

(** **** Exercise: (value_is_nf)  *)
Lemma value_is_nf : forall t,
  value t -> step_normal_form t.
Proof.
  unfold normal_form. unfold not. intros. destruct H0.
  generalize dependent x.
  induction t; intros; try solve_by_invert;
  try (solve_by_invert 2);
  try (inversion H; try solve_by_invert; inversion H1; subst;
  inversion H0; subst; eauto).
Qed.

(** **** Exercise: (succ_hastype_nat__hastype_nat)  *)
Example succ_hastype_nat__hastype_nat : forall t,
  |- tsucc t \in TNat ->
  |- t \in TNat.
Proof.
  intros. inversion H. assumption.
Qed.


(** **** Exercise: (finish_progress)  *)
(** Complete the formal proof of the [progress] property.  (Make sure
    you understand the informal proof fragment in the following
    exercise before starting -- this will save you a lot of time.) *)

Theorem progress : forall t T,
  |- t \in T ->
  value t \/ exists t', t ==> t'.
Proof with auto.
  intros t T HT.
  induction HT; auto.
  (* The cases that were obviously values, like T_True and
     T_False, were eliminated immediately by auto *)
  - (* T_If *)
    right. inversion IHHT1; clear IHHT1.
    + (* t1 is a value *)
    apply (bool_canonical t1 HT1) in H.
    inversion H; subst; clear H.
      exists t2. apply ST_IfTrue.
      exists t3. apply ST_IfFalse.
    + (* t1 can take a step *)
      inversion H as [t1' H1].
      exists (tif t1' t2 t3). apply ST_If with (t2:=t2) (t3 := t3) in H1 . 
      assumption.
  - (* T_Succ *) destruct IHHT.
    left. right. constructor.
     + apply (nat_canonical t1 HT) in H. auto.
     + right. inversion H. exists (tsucc x). apply ST_Succ in H0.
        assumption.
  - (* T_Pred *)
    destruct IHHT.
    + right.
    apply (nat_canonical t1 HT) in H. 
    inversion H. exists tzero. apply ST_PredZero. 
    exists t. apply ST_PredSucc. assumption.
    + right. inversion H. exists (tpred x). apply ST_Pred in H0. assumption.
  - (* T_Zero *)
    destruct IHHT.
    + right. apply (nat_canonical t1 HT) in H. inversion H.
    exists ttrue. apply ST_IszeroZero. 
    exists tfalse. apply ST_IszeroSucc. assumption.
    + right.
    destruct H. exists (tiszero x). apply ST_Iszero. assumption.
Qed.

Theorem preservation : forall t t' T,
  |- t \in T ->
  t ==> t' ->
  |- t' \in T.

(** **** Exercise: (finish_preservation)  *)
(** Complete the formal proof of the [preservation] property.  (Again,
    make sure you understand the informal proof fragment in the
    following exercise first.) *)

Proof with auto.
  intros t t' T HT HE.
  generalize dependent t'.
  induction HT;
         (* every case needs to introduce a couple of things *)
         intros t' HE;
         (* and we can deal with several impossible
            cases all at once *)
         try solve_by_invert.
    - (* T_If *) inversion HE; subst; clear HE.
      + (* ST_IFTrue *) assumption.
      + (* ST_IfFalse *) assumption.
      + (* ST_If *) apply T_If; try assumption.
        apply IHHT1; assumption.
    - (* T_Succ *) inversion HE; subst; clear HE. 
      apply T_Succ. apply IHHT. assumption.
    - (* T_Pred *) inversion HE; subst; clear HE.
      + assumption.
      + apply succ_hastype_nat__hastype_nat in HT. assumption.
      + apply IHHT in H0. apply T_Pred in H0. assumption.
    - (* T_Bool *) inversion HE; subst; clear HE; constructor.
      apply IHHT in H0. assumption.
Qed.

(** **** Exercise: (normalize_ex)  *)
Theorem normalize_ex : exists e',
  (AMult (ANum 3) (AMult (ANum 2) (ANum 1))) / empty_state
  ==>a* e'.
Proof.
  eapply ex_intro. normalize. Qed.
  
(** **** Exercise: (normalize_ex')  *)
(** For comparison, prove it using [apply] instead of [eapply]. *)

Theorem normalize_ex' : exists e',
  (AMult (ANum 3) (AMult (ANum 2) (ANum 1))) / empty_state
  ==>a* e'.
Proof.
  eapply ex_intro. normalize. 
Qed.

