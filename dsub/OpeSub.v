(** printing ⊢k #&vdash;<sub>k</sub># *)
(** printing ⊢! #&vdash;# *)
(** printing k⊣ #&dashv;# *)
(** printing |- #&vdash;# *)
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
 and examines its properties. In a nutshell, this concept captures weakening and
 narrowing at the same time, which serves very well when examine more than one
 contexts at the same time.
 *)

Reserved Notation "G1 ⊆<⦂ G2" (at level 90).
Inductive ope_sub : env -> env -> Prop :=
(** [――――――] Ope-Nil #<br>#
    [⋅ ⊆<⦂ ⋅]  *)
| os_nil : nil ⊆<⦂ nil
(** [G2 ⊆<⦂ G1] #<br>#
    [――――――――――――――――] Ope-Drop #<br>#
    [G2 ; x : T ⊆<⦂ G1]  *)
| os_drop : forall G1 G2 x T,
    G2 ⊆<⦂ G1 ->
    (x, T) :: G2 ⊆<⦂ G1
(** [G2 ⊆<⦂ G1] #<br>#
    [G2 ⊢ T1 <: T2] #<br>#
    [――――――――――――――――] Ope-Keep #<br>#
    [G2 ; x : T1 ⊆<⦂ G1 ; x : T2]  *)
| os_keep : forall G1 G2 x T1 T2,
    G2 ⊆<⦂ G1 ->
    G2 ⊢ T1 <⦂ T2 ->
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
      G' ⊢ trm_var (avar_f x) ⦂ T.
  Proof.
    induction on ope_sub; intros.
    - routine.
    - apply IHope_sub in H.
      reassoc 2 with 1. apply weaken_typing.
      trivial.
    - tidy_up.
      + eapply ty_sub; simpl_env; eauto.
      + apply IHope_sub in H0.
        simpl_env. apply weaken_typing.
        trivial.
  Qed.
  Hint Resolve ope_narrow_var.
  
  Lemma ope_narrow_trm : forall G t T,
      G ⊢ t ⦂ T ->
      forall G',
        G' ⊆<⦂ G ->
        G' ⊢ t ⦂ T
  with ope_narrow_subty : forall G T U,
      G ⊢ T <⦂ U ->
      forall G',
        G' ⊆<⦂ G ->
        G' ⊢ T <⦂ U.
  Proof.
    - clear ope_narrow_trm.
      induction on typing; intros; eauto.
      + econstructor. cofinite.
        apply H0; simpl; auto.
      + econstructor; auto. cofinite.
        apply H0; simpl; auto.
      + eapply ty_sub; eauto.
        
    - clear ope_narrow_subty.
      induction on subty; intros; eauto.

      eapply st_all. auto.
      cofinite.
      apply H0; simpl; auto.
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

End OpeProperties.  
