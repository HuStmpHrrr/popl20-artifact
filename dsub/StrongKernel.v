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
Require Import Stareat.
Require Import Step.
Require Import Kernel.
Require Import Misc.
Require Import ListRelations.
Require Import StructuralProperties.
Require Import OperationProperties.
Require Import OpeSub.

(** * Definition and Properties of Strong Kernel D#<sub>&lt;:</sub>#

    This file defines strong kernel D#<sub>&lt;:</sub># and examines its properties.
 *)

Reserved Notation "[ L ] G1 ⊢k S <⦂ U k⊣ G2" (at level 70).
Inductive subtysk : vars -> env -> typ -> typ -> env -> Prop :=
(** [―――――――――――――――――――――] SK-VRefl #<br>#
    [G1 ⊢k x.A <: x.A ⊣ G2] *)
| ssk_refl : forall L G1 G2 x,
    [ L ] G1 ⊢k typ_sel x <⦂ typ_sel x k⊣ G2
(** [―――――――――――――――――] SK-Top #<br>#
    [G1 ⊢k T <: ⊤ ⊣ G2] *)
| ssk_top : forall L G1 G2 T,
    [ L ] G1 ⊢k T <⦂ typ_top k⊣ G2
(** [―――――――――――――――――] SK-Bot #<br>#
    [G1 ⊢k ⊥ <: T ⊣ G2] *)
| ssk_bot : forall L G1 G2 T,
    [ L ] G1 ⊢k typ_bot <⦂ T k⊣ G2
(** [G1 ⊢k T1 >: S ⊣ G2] #<br>#
    [G1 ⊢k T2 <: U ⊣ G2] #<br>#
    [―――――――――――――――――――――――――――――――――――――――――] SK-Bnd #<br>#
    [G1 ⊢k {A : T1 .. T2} <: {A : S .. U} ⊣ G2] *)
| ssk_bnd : forall L G1 G2 S T1 T2 U,
    [ L ] G2 ⊢k S <⦂ T1 k⊣ G1 ->
    [ L ] G1 ⊢k T2 <⦂ U k⊣ G2 ->
    [ L ] G1 ⊢k typ_bnd T1 T2 <⦂ typ_bnd S U k⊣ G2
(** [G1 ⊢k T1 >: T2 ⊣ G2] #<br>#
    [G1 ; x : T1 ⊢k U1 <: U2 ⊣ G2] #<br>#
    [―――――――――――――――――――――――――――――――――――――] SK-All #<br>#
    [G1 ⊢k ∀(x : T1)U1 <: ∀(x : T2)U2 ⊣ G2] *)
| ssk_all : forall L G1 G2 T1 T2 U1 U2 x,
    x `notin` fv G1 `union` fv T1 `union` fv T2
      `union` fv U1 `union` fv U2 `union` fv G2 `union` L ->
    [ L ] G2 ⊢k T2 <⦂ T1 k⊣ G1 ->
    [ union L (union (singleton x) (fv T2)) ]
      x ~ T1 ++ G1 ⊢k open x U1 <⦂ open x U2 k⊣ x ~ T2 ++ G2 ->
    [ L ] G1 ⊢k typ_all T1 U1 <⦂ typ_all T2 U2 k⊣ G2
(** [G1 ⊢k G(x) >: {A : S .. ⊤} ⊣ G2] #<br>#
    [―――――――――――――――――――――――――――――――] SK-Sel1 #<br>#
    [G1 ⊢k S <: x.A ⊣ G2] *)
| ssk_sel1 : forall L G1 G2 x T S,
    binds x T G2 ->
    [ L ] G2 ⊢k T <⦂ typ_bnd S typ_top k⊣ G1 ->
    [ L ] G1 ⊢k S <⦂ typ_sel $ avar_f x k⊣ G2
(** [G1 ⊢k G(x) <: {A : ⊥ .. U} ⊣ G2] #<br>#
    [―――――――――――――――――――――――――――――――] SK-Sel2 #<br>#
    [G1 ⊢k x.A <: U ⊣ G2] *)
| ssk_sel2 : forall L G1 G2 x T U,
    binds x T G1 ->
    [ L ] G1 ⊢k T <⦂ typ_bnd typ_bot U k⊣ G2 ->
    [ L ] G1 ⊢k typ_sel $ avar_f x <⦂ U k⊣ G2
where "[ L ] G1 ⊢k S <⦂ U k⊣ G2" := (subtysk L G1 S U G2).
Hint Constructors subtysk.

(** *** Reflexivity of strong kernel D#<sub>&lt;:</sub># *)
Program Fixpoint subtysk_refl T {measure (typ_struct_measure T)} :
  forall L G1 G2,
    [ L ] G1 ⊢k T <⦂ T k⊣ G2 := _.
Next Obligation.
  destruct T; eauto.
  - pick_fresh x. econstructor; eauto.
    + apply subtysk_refl.
      simpl; lia.
    + apply subtysk_refl. autorewrite with measures.
      simpl; lia.
  - constructor; apply subtysk_refl; simpl; lia.
Qed.

Local Hint Resolve subtysk_refl.

(** ** Strong Kernel D#<sub>&lt;:</sub># Subsuming Kernel D#<sub>&lt;:</sub># *)
Theorem subtykn_to_subtysk : forall L G S U,
    subtykn L G S U ->
    [ L ] G ⊢k S <⦂ U k⊣ G.
Proof.
  induction on subtykn; eroutine.
Qed.

(** ** Soundness and Completeness of Stare-at Subtyping w.r.t. Strong Kernel D#<sub>&lt;:</sub># *)

(** *** The soundness theorem *)
Lemma subtysk_sound_gen : forall L G1 S U G2,
    [L] G1 ⊢k S <⦂ U k⊣ G2 ->
    forall G,
      fv G [<=] L ->
      uniq G ->
      G ⊆<⦂ G1 ->
      G ⊆<⦂ G2 ->
      G ⊢ S <⦂ U.
Proof.
  induction on subtysk; try solve [routine]; intros.
  - eapply st_all; eauto.
    cofinite.
    apply open_subst_subty with (x := x); auto; clear Fr.
    + fsetdec.
    + apply IHsubtysk2.
      * set solve.
      * constructor; trivial.
        simpl in *. fsetdec.
      * simpl; auto using os_keep.
      * simpl; auto using os_keep.
  - apply ty_var in H.
    eapply ope_narrow_trm in H; eauto.
    eauto using ty_sub.
  - apply ty_var in H.
    eapply ope_narrow_trm in H; eauto.
    eauto using ty_sub.
Qed.

Lemma subtysk_sound : forall G S U,
    [ fv G ] G ⊢k S <⦂ U k⊣ G ->
    uniq G ->
    G ⊢ S <⦂ U.
Proof.
  intros. eauto using subtysk_sound_gen, ope_sub_refl.
Qed.

(** *** The completeness theorem *)

(** Similar to the situation in kernel D#<sub>&lt;:</sub>#, it is easier to establish the completeness
proof via a variant where contexts are not truncated, so that the inductive hypothesis
will be much easier to work with. *)
Reserved Notation "[ L ] G1 >> T '<⦂p' U << G2" (at level 70).
Inductive stareat' : atoms -> env -> typ -> typ -> env -> Prop :=
| bs'_bot : forall L G1 T G2, [ L ] G1 >> typ_bot <⦂p T << G2
| bs'_top : forall L G1 T G2, [ L ] G1 >> T <⦂p typ_top << G2
| bs'_sel_refl : forall L G1 x G2, [ L ] G1 >> typ_sel x <⦂p typ_sel x << G2
| bs'_sel_left : forall L G1 x G2 T U,
    upcast_e' G1 x T ->
    [ L ] G1 >> T <⦂p U << G2 ->
    [ L ] G1 >> typ_sel x <⦂p U << G2
| bs'_sel_right : forall L G1 x G2 T U,
    downcast_e' G2 x U ->
    [ L ] G1 >> T <⦂p U << G2 ->
    [ L ] G1 >> T <⦂p typ_sel x << G2

| bs'_all : forall L G1 T1 U1 G2 T2 U2 x,
    x `notin` fv G1 `union` fv T1 `union` fv T2
      `union` fv U1 `union` fv U2 `union` fv G2 `union` L ->
    [ L ] G2 >> T2 <⦂p T1 << G1 ->
    [ L  `union` singleton x `union` fv T2 ]
      x ~ T1 ++ G1 >> open x U1 <⦂p open x U2 << x ~ T2 ++ G2 ->
    [ L ] G1 >> typ_all T1 U1 <⦂p typ_all T2 U2 << G2
| bs'_bnd : forall L G1 S1 U1 S2 U2 G2,
    [ L ] G2 >> S2 <⦂p S1 << G1 ->
    [ L ] G1 >> U1 <⦂p U2 << G2 ->
    [ L ] G1 >> typ_bnd S1 U1 <⦂p typ_bnd S2 U2 << G2
where "[ L ] G1 >> T '<⦂p' U << G2" := (stareat' L G1 T U G2)%type.
Local Hint Constructors stareat' stareat.

Local Hint Constructors ope_list.
Local Hint Resolve ope_list_trans ope_list_refl ope_list_to_nil.
Local Hint Resolve ope_list_trans ope_list_append2.

Local Ltac wf_env :=
  lazymatch goal with
  | H : wf_env (_ ++ _) |- _ => apply wf_deapp in H; invert H; subst
  end.

(** First show that the alternative definition of stare-at subtyping is the same
as the previous one. *)
Lemma stareat'_to_stareat : forall L G1 S U G2,
    [ L ] G1 >> S <⦂p U << G2 ->
    wf_env G1 -> wf_env G2 ->
    fv S [<=] dom G1 -> lc S ->
    fv U [<=] dom G2 -> lc U ->
    [ L ] G1 >> S <⦂ U << G2.
Proof.
  induction on stareat'; intros; try solve [routine].
  - destruct H.
    + econstructor.
      * apply uc_top.
      * rec_pose IHstareat' H; set solve.
        eapply stareat_strengthening with (G := G); eroutine.
    + pose proof H.
      apply binds_app in H; destruct_conjs; subst.
      apply exposure'_to_exposure in H7; trivial.
      pose proof H0. wf_env.
      apply exposure_to_revealing in H7; set solve.
      destruct_conjs.
      apply revealing_strengthening with (G' := H9) in H11; eauto.
      destruct_conjs.

      econstructor; eauto.
      eapply uc_bot. eassumption.
    + pose proof H.
      apply binds_app in H; destruct_conjs; subst.
      apply exposure'_to_exposure in H7; trivial.
      pose proof H0. wf_env.
      apply exposure_to_revealing in H7; set solve.
      destruct_conjs.
      apply revealing_strengthening with (G' := H9) in H11; eauto.
      destruct_conjs.

      econstructor.
      * eapply uc_bnd. eassumption.
      * pose proof H12.
        apply revealing_preserves_wf in H12; trivial.
        destruct_conjs.
        progressive_inversions.
        apply revealing_gives_prefix in H18.
        pose proof (prefix_dom H18).
        rec_pose IHstareat' Hind; set solve.

        apply prefix_to_app in H18. destruct_conjs.
        subst.
        eapply stareat_strengthening; eroutine.

  - destruct H.
    + econstructor.
      * apply dc_bot.
      * rec_pose IHstareat' H; set solve.
        eapply stareat_strengthening with (D := G); eroutine.
    + pose proof H.
      apply binds_app in H; destruct_conjs; subst.
      apply exposure'_to_exposure in H7; trivial.
      pose proof H1. wf_env.
      apply exposure_to_revealing in H7; set solve.
      destruct_conjs.
      apply revealing_strengthening with (G' := H9) in H11; eauto.
      destruct_conjs.

      econstructor; eauto.
      eapply dc_top. eassumption.
    + pose proof H.
      apply binds_app in H; destruct_conjs; subst.
      apply exposure'_to_exposure in H7; trivial.
      pose proof H1. wf_env.
      apply exposure_to_revealing in H7; set solve.
      destruct_conjs.
      apply revealing_strengthening with (G' := H9) in H11; eauto.
      destruct_conjs.

      econstructor.
      * eapply dc_bnd. eassumption.
      * pose proof H12.
        apply revealing_preserves_wf in H12; trivial.
        destruct_conjs.
        progressive_inversions.
        apply revealing_gives_prefix in H18.
        pose proof (prefix_dom H18).
        rec_pose IHstareat' Hind; set solve.

        apply prefix_to_app in H18. destruct_conjs.
        subst.
        eapply stareat_strengthening; eroutine.

  - eapply sa_all with x; simpl in *; progressive_inversions; fold_cls.
    + set solve.
    + auto.
    + apply IHstareat'2.
      all:auto using open_lc_typ.
      all:try constructor; auto.
      * pose proof (fv_open_typ U1 x 0).
        etransitivity; [ eassumption |].
        set solve.
      * pose proof (fv_open_typ U2 x 0).
        etransitivity; [ eassumption |].
        set solve.
Qed.

Local Hint Constructors upcast_e' downcast_e'.
Local Hint Resolve exposure'_weakening_gen exposure_to_exposure'.

Lemma stareat'_weakening_gen: forall L' G1 G2 S U G3 G4,
    [ L' ] G1 ++ G2 >> S <⦂p U << G3 ++ G4 ->
    forall G G' L,
      L' [=] L `union` fv G' `union` fv G ->
      [ L ] G1 ++ G ++ G2 >> S <⦂p U << G3 ++ G' ++ G4.
Proof.
  intros. dependent induction H; intros; eroutine.
  - dependent destruction H; eauto 6.
  - dependent destruction H; eauto 6.
  - eapply bs'_all with x.
    + change (union (dom (G1 ++ G2)) (fv_values fv_typ (G1 ++ G2)))
        with (fv (G1 ++ G2)) in *.
      change (union (dom (G3 ++ G4)) (fv_values fv_typ (G3 ++ G4)))
        with (fv (G3 ++ G4)) in *.
      change (union (dom G) (fv_values fv_typ G)) with (fv G) in *.
      change (union (dom G') (fv_values fv_typ G')) with (fv G') in *.
      repeat rewrite fv_union in *. fold_cls.
      fsetdec.
    + apply IHstareat'1; trivial.
      rewrite H2. clear H H2. fsetdec.
    + reassoc 4 with 3.
      replace (x ~ T2 ++ nil ++ G3 ++ G' ++ G4) with
          ((x ~ T2 ++ G3) ++ G' ++ G4).
            
      apply IHstareat'2; try solve [routine].
      * rewrite H2. clear H H2. fsetdec.
      * simpl_env. trivial.
  - constructor.
    + apply IHstareat'1; trivial.
      rewrite H1. fsetdec.
    + apply IHstareat'2; trivial.
Qed.

Lemma stareat'_weakening_l: forall L G1 G2 S U G,
    [ L `union` fv G ] G1 >> S <⦂p U << G2 ->
    [ L ] G ++ G1 >> S <⦂p U << G2.
Proof.
  intros.
  change (G ++ G1) with (nil ++ G ++ G1).
  change G2 with (nil ++ nil ++ G2).
  eapply stareat'_weakening_gen; eauto.
  simpl. fsetdec.
Qed.
  
Lemma stareat'_weakening_r: forall L G1 G2 S U G,
    [ L `union` fv G ] G1 >> S <⦂p U << G2 ->
    [ L ] G1 >> S <⦂p U << G ++ G2.
Proof.
  intros.
  change (G ++ G2) with (nil ++ G ++ G2).
  change G1 with (nil ++ nil ++ G1).
  eapply stareat'_weakening_gen; eauto.
  simpl. fsetdec.
Qed.

Lemma revealing_fv_bound : forall G S G' U,
    revealing G S G' U ->
    fv U [<=] fv G `union` fv S.
Proof.
  induction on revealing; set solve.

  apply revealing_gives_prefix in H3_.
  apply prefix_to_app in H3_.
  destruct_conjs. subst.
  set simpl in *. simpl in *. fold_cls.
  fsetdec.
Qed.

Lemma stareat_to_stareat' : forall L' G1 S U G2,
    [ L' ] G1 >> S <⦂ U << G2 ->
    forall L,
      L `union` fv G1 `union` fv G2 `union` fv S `union` fv U [<=] L' ->
    [ L ] G1 >> S <⦂p U << G2.
Proof.
  induction on stareat; intros; eauto.
  - destruct H; eauto.
    + econstructor; eauto.
      rewrite <- (app_nil_2 _ G).
      apply stareat'_weakening_l.
      apply IHstareat.
      change (fv nil) with (union empty empty).
      fsetdec.
      
    + econstructor.
      * eapply ue_bot. eauto.
        apply revealing_to_exposure in H.
        apply exposure_to_exposure'.
        auto using exposure_weakening.
      * rewrite <- (app_nil_2 _ G1).
        repeat apply stareat'_weakening_l.
        apply IHstareat.
        repeat rewrite fv_union in *.
        change (fv nil) with (union empty empty).
        fsetdec.

    + econstructor.
      * eapply ue_bnd. eauto.
        apply revealing_to_exposure in H.
        apply exposure_to_exposure'.
        eauto using exposure_weakening.
      * pose proof (revealing_gives_prefix H).
        apply prefix_to_app in H1. destruct_conjs.
        subst. 
        do 3 apply stareat'_weakening_l.
        apply IHstareat.
        apply revealing_fv_bound in H.
        repeat rewrite fv_union in *.
        assert (fv U0 [<=] L). {
          simpl in *. fsetdec.
        }        
        fsetdec.

  - destruct H; eauto.
    + econstructor; eauto.
      rewrite <- (app_nil_2 _ G).
      apply stareat'_weakening_r.
      apply IHstareat.
      change (fv nil) with (union empty empty).
      fsetdec.
      
    + econstructor.
      * eapply de_top. eauto.
        apply revealing_to_exposure in H.
        apply exposure_to_exposure'.
        auto using exposure_weakening.
      * rewrite <- (app_nil_2 _ G0).
        repeat apply stareat'_weakening_r.
        apply IHstareat.
        repeat rewrite fv_union in *.
        change (fv nil) with (union empty empty).
        fsetdec.

    + econstructor.
      * eapply de_bnd. eauto.
        apply revealing_to_exposure in H.
        apply exposure_to_exposure'.
        eauto using exposure_weakening.
      * pose proof (revealing_gives_prefix H).
        apply prefix_to_app in H1. destruct_conjs.
        subst. 
        do 3 apply stareat'_weakening_r.
        apply IHstareat.
        apply revealing_fv_bound in H.
        repeat rewrite fv_union in *.
        assert (fv L1 [<=] L). {
          simpl in *. fsetdec.
        }        
        fsetdec.

  - apply bs'_all with x.
    + fsetdec.
    + apply IHstareat1. clear H.
      simpl in *. fsetdec.
    + apply IHstareat2. clear H.
      repeat rewrite fv_union.
      pose proof (fv_open_typ U1 x 0).
      pose proof (fv_open_typ U2 x 0).
      simpl in *. fsetdec.
  - constructor.
    + apply IHstareat1. simpl in *.
      fsetdec.
    + apply IHstareat2. simpl in *.
      fsetdec.
Qed.    

(** Similar to kernel D#<sub>&lt;:</sub>#, in strong kernel D#<sub>&lt;:</sub>#, transitivity holds on [⊤] and [⊥]. *)
Lemma sk_trans_on_top : forall L G1 T G2,
    [ L ] G1 ⊢k typ_top <⦂ T k⊣ G2 ->
    forall S,
      [ L ] G1 ⊢k S <⦂ T k⊣ G2
with layered_top_trans : forall L G1 T l U G2,
    [ L ] G1 ⊢k T <⦂ bnd_layer (typ_bnd typ_top U) l k⊣ G2 ->
    forall S,
      [ L ] G1 ⊢k T <⦂ bnd_layer (typ_bnd S U) l k⊣ G2.
Proof.
  - clear sk_trans_on_top.
    dep induction on subtysk; routine.
    econstructor; eauto.
    apply layered_top_trans with (l := nil).
    assumption.

  - clear layered_top_trans.
    intros. gen S.
    dependent induction H; intros; eauto.
    1-5:induction l; eroutine.

    econstructor; eauto.
    specialize (IHsubtysk (cons _ l) U eq_refl).
    simpl in IHsubtysk. auto.
Qed.
Local Hint Resolve sk_trans_on_top.

Lemma sk_trans_on_bot : forall L G1 T G2,
    [ L ] G1 ⊢k T <⦂ typ_bot k⊣ G2 ->
    forall U,
      [ L ] G1 ⊢k T <⦂ U k⊣ G2
with layered_bot_trans : forall L G1 T l S G2,
    [ L ] G1 ⊢k T <⦂ bnd_layer (typ_bnd S typ_bot) l k⊣ G2 ->
    forall U,
      [ L ] G1 ⊢k T <⦂ bnd_layer (typ_bnd S U) l k⊣ G2.
Proof.
  - clear sk_trans_on_bot.
    dep induction on subtysk; routine.
    econstructor; eauto.
    apply layered_bot_trans with (l := nil).
    assumption.

  - clear layered_bot_trans.
    intros. gen U.
    dependent induction H; intros; eauto.
    1-5:induction l; eroutine.

    econstructor; eauto.
    specialize (IHsubtysk (cons _ l) S eq_refl).
    simpl in IHsubtysk. auto.
Qed.
Local Hint Resolve sk_trans_on_bot.

(** Then we show that the alternative definition of [Exposure] is compatible with
strong kernel.  *)
Theorem exposure'_to_subtysk : forall G S U,
    exposure' G S U ->
    forall G' L U',
      [ L ] G ⊢k U <⦂ U' k⊣ G' ->
      [ L ] G ⊢k S <⦂ U' k⊣ G'.
Proof.
  induction on exposure'.
  1,2,4:eroutine.
  routine.
  econstructor; try eassumption.
  eauto.
Qed.
Local Hint Resolve exposure'_to_subtysk.

(** Then we recover [Revealing] by considering its connection with the alternative
[Exposure]. *)
Theorem revealing_to_subtysk : forall G S G'' U,
    revealing G S G'' U ->
    forall G' L U',
      [ L ] G ⊢k U <⦂ U' k⊣ G' ->
      [ L ] G ⊢k S <⦂ U' k⊣ G'.
Proof.
  intros.
  eapply exposure'_to_subtysk; 
  eauto 10 using exposure_to_exposure', revealing_to_exposure.
Qed.

Theorem stareat'_to_subtysk : forall L G1 S U G2,
    [ L ] G1 >> S <⦂p U << G2 ->
    [ L ] G1 ⊢k S <⦂ U k⊣ G2.
Proof.
  induction on stareat'; routine.
  - destruct H; auto.
    + econstructor. eauto.
      eauto.
    + eauto.
  - destruct H; auto.
    + econstructor. eauto.
      eauto.
    + eauto.
  - eauto.
Qed.

(** *** the soundness theorem *)
Lemma stareat_to_subtysk : forall L G1 S U G2,
    [ L `union` fv G1 `union` fv G2 `union` fv S `union` fv U ]
      G1 >> S <⦂ U << G2 ->
    [ L ] G1 ⊢k S <⦂ U k⊣ G2.
Proof.
  intros.
  eauto using stareat'_to_subtysk, stareat_to_stareat'.
Qed.

(** Very similar to kernel D#<sub>&lt;:</sub>#, here we define a "step-enriched" version of strong
kernel D#<sub>&lt;:</sub>#, in order to do a well-founded induction on the steps. *)
Inductive subtysk' : vars -> env -> typ -> typ -> env -> nat -> Prop :=
| ssk'_refl : forall L G1 G2 x, subtysk' L G1 (typ_sel x) (typ_sel x) G2 1
| ssk'_top : forall L G1 G2 T, subtysk' L G1 T typ_top G2 1
| ssk'_bot : forall L G1 G2 T, subtysk' L G1 typ_bot T G2 1
| ssk'_bnd : forall L G1 G2 S T1 T2 U n1 n2,
    subtysk' L G2 S T1 G1 n1 -> subtysk' L G1 T2 U G2 n2 ->
    subtysk' L G1 (typ_bnd T1 T2) (typ_bnd S U) G2 (1 + n1 + n2)
| ssk'_all : forall L G1 G2 T1 T2 U1 U2 x n1 n2,
    x `notin` fv G1 `union` fv T1 `union` fv T2
      `union` fv U1 `union` fv U2 `union` fv G2 `union` L ->
    subtysk' L G2 T2 T1 G1 n1 ->
    subtysk' (union L (union (singleton x) (fv T2)))
            (x ~ T1 ++ G1) (open x U1) (open x U2) (x ~ T2 ++ G2) n2 ->
    subtysk' L G1 (typ_all T1 U1) (typ_all T2 U2) G2 (1 + n1 + n2)
| ssk'_sel1 : forall L G1 G2 x T S n,
    binds x T G2 ->
    subtysk' L G2 T (typ_bnd S typ_top) G1 n ->
    subtysk' L G1 S (typ_sel $ avar_f x) G2 (1 + n)
| ssk'_sel2 : forall L G1 G2 x T U n,
    binds x T G1 ->
    subtysk' L G1 T (typ_bnd typ_bot U) G2 n ->
    subtysk' L G1 (typ_sel $ avar_f x) U G2 (1 + n).
Hint Constructors subtysk'.
Notation "[ L , n ] G1 ⊢k S <⦂ U k⊣ G2" := (subtysk' L G1 S U G2 n) (at level 70).


Lemma subtysk_to_subtysk' : forall L G1 S U G2,
    [ L ] G1 ⊢k S <⦂ U k⊣ G2 ->
    exists n, [ L , n ] G1 ⊢k S <⦂ U k⊣ G2.
Proof.
  induction on subtysk; eroutine.
Qed.

Lemma subtysk'_to_subtysk : forall L G1 S U G2 n,
    [ L , n ] G1 ⊢k S <⦂ U k⊣ G2 ->
    [ L ] G1 ⊢k S <⦂ U k⊣ G2.
Proof.
  induction on subtysk'; eroutine.
Qed.

(** This lemma shows the two definitions of strong kernel D#<sub>&lt;:</sub># coincide. *)
Lemma subtysk_equiv_subtysk' : forall L G1 S U G2,
    [ L ] G1 ⊢k S <⦂ U k⊣ G2 <->
    exists n, [ L , n ] G1 ⊢k S <⦂ U k⊣ G2.
Proof.
  split; auto using subtysk_to_subtysk'.
  intros. tidy_up.
  eauto using subtysk'_to_subtysk.
Qed.

Local Hint Extern 1 (_ <= _) => lia.
Local Hint Constructors exposure'.

(** We also need an auxiliary lemma to strenthen the inductive hpothesis. *)
Program Fixpoint subtysk'_conversions n {measure n} : forall L G1 S U G2,
    [ L , n ] G1 ⊢k S <⦂ U k⊣ G2 ->
    [ L ] G1 >> S <⦂p U << G2 /\
    (forall T1 T2,
        U = typ_bnd T1 T2 ->
        exists S', exposure' G1 S S' /\
              (S' = typ_bot \/
               exists T1' T2' n',
                 S' = typ_bnd T1' T2' /\
                 [ L ] G2 >> T1 <⦂p T1' << G1 /\
                 ([ L , n' ] G1 ⊢k T2' <⦂ T2 k⊣ G2) /\ n' <= n))
  := _.
Next Obligation.
  split; intros.
  - induction H; routine.
    + eapply bs'_all with x; auto.
    + clear IHsubtysk'.
      apply subtysk'_conversions in H0; auto.
      tidy_up.
      specialize (H1 _ _ eq_refl).
      tidy_up; eauto.
    + clear IHsubtysk'.
      apply subtysk'_conversions in H0; auto.
      tidy_up.
      specialize (H1 _ _ eq_refl).
      tidy_up; eauto.

      apply subtysk'_conversions in H8; auto.
      tidy_up. eauto.

  - destruct H; subst; progressive_inversions; eauto 10.

    + eexists. split; [apply ex_stop; auto |].
      right. repeat eexists; try eassumption; auto.
      eapply subtysk'_conversions; try eassumption.
      lia.
    + apply subtysk'_conversions in H1; try lia.
      tidy_up.
      specialize (H1 _ _ eq_refl).
      tidy_up; eauto.

      apply subtysk'_conversions in H8; try lia.
      tidy_up.
      specialize (H6 _ _ eq_refl).
      tidy_up; eauto 14.
Qed.

Theorem subtysk_to_stareat' : forall L G1 S U G2,
    [ L ] G1 ⊢k S <⦂ U k⊣ G2 ->
    [ L ] G1 >> S <⦂p U << G2.
Proof.
  intros. apply subtysk_to_subtysk' in H.
  tidy_up. eapply subtysk'_conversions.
  eassumption.
Qed.

(** Then the completeness theorem is established. *)
Theorem subtysk_to_stareat : forall L G1 S U G2,
    [ L ] G1 ⊢k S <⦂ U k⊣ G2 ->
    wf_env G1 -> wf_env G2 ->
    fv S [<=] dom G1 -> lc S ->
    fv U [<=] dom G2 -> lc U ->
    [ L ] G1 >> S <⦂ U << G2.
Proof.
  intros.
  auto using subtysk_to_stareat', stareat'_to_stareat.
Qed.

(* together with stareat_to_subtysk, we've shown that stare-at subtyping is
   equivalent to strong kernel D#<sub>&lt;:</sub>#, modulo name store.
 *)

Lemma stareat_cong_names : forall L G1 S U G2,
    [ L ] G1 >> S <⦂ U << G2 ->
    forall L',
      L [=] L' ->
      [ L' ] G1 >> S <⦂ U << G2.
Proof.
  induction on stareat; intros; eauto.
  eapply sa_all with x; auto.
  - fsetdec.
  - apply IHstareat2.
    clear H. fsetdec.
Qed.

(** Effectively, this theorem says, as long as free names are not reused, then these
    strong kernel D#<sub>&lt;:</sub># and stare-at subtyping induce the same language.
  *)
Theorem subtysk_equiv_stareat : forall L G1 S U G2,
    wf_env G1 -> wf_env G2 ->
    fv S [<=] dom G1 -> lc S ->
    fv U [<=] dom G2 -> lc U ->
    [ L `union` fv G1 `union` fv G2 `union` fv S `union` fv U ]
      G1 ⊢k S <⦂ U k⊣ G2 <->
    [ L `union` fv G1 `union` fv G2 `union` fv S `union` fv U ]
      G1 >> S <⦂ U << G2.
Proof.
  split; intros.
  - auto using subtysk_to_stareat.
  - apply stareat_to_subtysk; trivial.
    eapply stareat_cong_names; eauto.
    fsetdec.
Qed.
