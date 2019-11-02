(** printing ⊢k #&vdash;<sub>k</sub># *)
(** printing ⊢s #&vdash;<sub>s</sub># *)
(** printing ⊢! #&vdash;# *)
(** printing k⊣ #&dashv;# *)
(** printing |- #&vdash;# *)
(** printing ↗! #&nearrow;# *)
(** printing ↘! #&searrow;# *)
(** printing ⦂ #:# *)
(** printing <⦂ #<:# *)
(** printing [<=] #&subseteq;# *)
(** printing `union` #&cup;# *)
(** printing \u #&cup;# *)
(** printing `notin` #&notin;# *)
(** printing `in` #&in;# *)
(** printing ⊆<⦂ #&subseteq;<sub>&lt;:</sub># *)

Set Implicit Arguments.
Require Import Definitions.
Require Import OperationProperties.
Require Import StructuralProperties.

(** * OPE#<sub>&lt;:</sub>#

    This file defines the order-preserving sub-environment, or OPE#<sub>&lt;:</sub>#
 and examines its properties. This file is very similar to the one in
 D#<sub>&lt;:</sub># and thus will not be discussed further.
  *)
Reserved Notation "G1 ⊆<⦂ G2" (at level 90).
Inductive ope_sub : env -> env -> Prop :=
|  os_nil :
     nil ⊆<⦂ nil
| os_drop : forall (G1 G2 : env) (x : atom) (T : typ),
    G2 ⊆<⦂ G1 ->
    (x, T) :: G2 ⊆<⦂ G1
| os_keep : forall (G1 G2 : env) (x : atom) (T1 T2 : typ),
    G2 ⊆<⦂ G1 ->
    G2 ⊢F T1 <⦂ T2 ->
    (x, T1) :: G2 ⊆<⦂ (x, T2) :: G1
where "G1 ⊆<⦂ G2" := (ope_sub G2 G1).
Local Hint Constructors ope_sub.

Section OpeProperties.

  Lemma ope_sub_length : forall G1 G2,
    G2 ⊆<⦂ G1 -> 
    length G1 <= length G2.
  Proof.
    induction on ope_sub; routine.
  Qed.
  
  Hint Resolve weaken_subty.

  Lemma ope_narrow_var :
    forall G G' x T,
      G' ⊆<⦂ G ->
      binds x T G ->
      exists T', binds x T' G' /\ (G' ⊢F T' <⦂ T).
  Proof.
    induction on ope_sub; intros.
    - routine.
    - apply IHope_sub in H.
      tidy_up.
      eexists; split; eauto.
      simpl_env; eauto.
    - tidy_up.
      + eexists; split; eauto.
        simpl_env; eauto.
      + apply IHope_sub in H0.
        tidy_up.
        eexists; split; eauto.
        simpl_env; eauto.
  Qed.
  
  Hint Resolve subty_refl subty_trans.

  Lemma ope_narrow_subty : forall G T U,
      G ⊢F T <⦂ U ->
      forall G',
        G' ⊆<⦂ G ->
        G' ⊢F T <⦂ U.
  Proof.
    induction on subty; intros; eauto 4.
    - eapply ope_narrow_var in H; eroutine.
    - eapply st_all. auto.
      cofinite. eroutine.
  Qed.
  Hint Resolve ope_narrow_subty.
  
  Lemma ope_sub_trans : forall G1 G2 G3,
      G2 ⊆<⦂ G1 ->
      G3 ⊆<⦂ G2 ->
      G3 ⊆<⦂ G1.
  Proof.
    intros. gen G1. induction H0; intros; auto.
    invert H1; subst; eauto.
  Qed.

  Lemma ope_sub_refl : forall G,
      G ⊆<⦂ G.
  Proof. induction on env; routine. Qed.

  Lemma ope_sub_nil : forall G,
      G ⊆<⦂ nil.
  Proof. induction on env; routine. Qed.

  Lemma ope_sub_app : forall G G1 G2,
      G2 ⊆<⦂ G ->
      G1 ++ G2 ⊆<⦂ G.
  Proof. induction G1; routine. Qed.

  Lemma ope_sub_app_r : forall G G1 G2,
      G ⊆<⦂ G1 ++ G2 ->
      G ⊆<⦂ G2.
  Proof.
    dep induction on ope_sub; eroutine.
    - destruct H0, H1; routine.
    - destruct H0; routine.
      specialize (IHope_sub H0 H1 eq_refl).
      auto.
  Qed.
  
End OpeProperties.  
