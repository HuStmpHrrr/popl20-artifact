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
Require Import Step.
Require Import Misc.
Require Import ListRelations.
Require Import StructuralProperties.
Require Import OperationProperties.

(** * Definition and Properties of Kernel D#<sub>&lt;:</sub>#
    
    This file defines Kernel D#<sub>&lt;:</sub># and examines its properties.
 *)

Reserved Notation "[ L ] G ⊢k S <⦂ U" (at level 70).
Inductive subtykn : vars -> env -> typ -> typ -> Prop :=
(** [―――――――――――――――] K-VRefl #<br>#
    [G ⊢k x.A <: x.A] *)
| snf_vrefl : forall L G x,
    [ L ] G ⊢k typ_sel x <⦂ typ_sel x
(** [―――――――――――] K-Top #<br>#
    [G ⊢k T <: ⊤] *)
| snf_top : forall L G T,
    [ L ] G ⊢k T <⦂ typ_top
(** [―――――――――――] K-Bot #<br>#
    [G ⊢k ⊥ <: T] *)
| snf_bot : forall L G T,
    [ L ] G ⊢k typ_bot <⦂ T
(** [G ⊢k S <: T1] #<br>#
    [G ⊢k T2 <: U] #<br>#
    [―――――――――――――――――――――――――――――――――――] K-Bnd #<br>#
    [G ⊢k {A : T1 .. T2} <: {A : S .. U}] *)
| snf_bnd : forall L G S T1 T2 U,
    [ L ] G ⊢k S <⦂ T1 ->
    [ L ] G ⊢k T2 <⦂ U ->
    [ L ] G ⊢k typ_bnd T1 T2 <⦂ typ_bnd S U
(** [G ; x : T ⊢k U1 <: U2] #<br>#
    [―――――――――――――――――――――――――――――] K-All #<br>#
    [G ⊢k ∀(x : T)U1 <: ∀(x : T)U2] *)
| snf_all : forall L G T U1 U2 x,
    x `notin` union (fv G)
      (union (fv T) (union (fv U1) (union (fv U2) L))) ->
    [ union L (union (singleton x) (fv T)) ]
      x ~ T ++ G ⊢k open x U1 <⦂ open x U2 ->
    [ L ] G ⊢k typ_all T U1 <⦂ typ_all T U2
(** [G ⊢k G(x) <: {A : S .. ⊤}] #<br>#
    [―――――――――――――――――――――――――] K-Sel1 #<br>#
    [G ⊢k S <: x.A] *)
| snf_sel1 : forall L G x T S,
    binds x T G ->
    [ L ] G ⊢k T <⦂ typ_bnd S typ_top ->
    [ L ] G ⊢k S <⦂ (typ_sel $ avar_f x)
(** [G ⊢k G(x) <: {A : ⊥ .. U}] #<br>#
    [―――――――――――――――――――――――――] K-Sel2 #<br>#
    [G ⊢k x.A <: U] *)
| snf_sel2 : forall L G x T U,
    binds x T G ->
    [ L ] G ⊢k T <⦂ typ_bnd typ_bot U ->
    [ L ] G ⊢k typ_sel $ avar_f x <⦂ U
where "[ L ] G ⊢k S <⦂ U" := (subtykn L G S U).
Hint Constructors subtykn.

Program Fixpoint subtykn_refl T {measure (typ_struct_measure T)} :
  forall L G,
    [ L ] G ⊢k T <⦂ T := _.
Next Obligation.
  destruct T; eauto.
  - pick_fresh x. econstructor; eauto.
    apply subtykn_refl. autorewrite with measures.
    simpl; lia.
  - constructor; apply subtykn_refl; simpl; lia.
Qed.

Lemma subtykn_sound : forall L G S U,
    [ L ] G ⊢k S <⦂ U ->
    uniq G ->
    G ⊢ S <⦂ U.
Proof.
  induction on subtykn; routine.
  - eapply st_all; trivial.
    cofinite.
    apply open_subst_subty with (x := x); auto.
  - eauto using ty_sub.
  - eauto using ty_sub.
Qed.

Lemma weaken_subtykn_gen : forall L' G1 G2 S U,
    [ L' ] G1 ++ G2 ⊢k S <⦂ U ->
    forall L G,
      L' [=] L `union` fv G ->
      [ L ] G1 ++ G ++ G2 ⊢k S <⦂ U.
Proof.
  dep induction on subtykn; eroutine.
  econstructor.
  - instantiate (1 := x). rewrite H2 in *.
    change (union (dom (H0 ++ H1)) (fv_values fv_typ (H0 ++ H1)))
      with (fv (H0 ++ H1)) in H.
    change (union (dom G) (fv_values fv_typ G)) with (fv G) in H.
    repeat rewrite fv_union in *.
    fold_cls. fsetdec.
  - reassoc 4 with 3.
    eapply IHsubtykn; auto.
    rewrite H2.
    change (union (dom G) (fv_values fv_typ G)) with (fv G).
    clear H. fold_cls.
    fsetdec.
Qed.

Lemma weaken_subtykn : forall L G G' S U,
    [ L `union` fv G' ] G ⊢k S <⦂ U -> [ L ] G' ++ G ⊢k S <⦂ U.
Proof.
  intros. reassoc 2 with 0.
  eapply weaken_subtykn_gen; eauto.
  fsetdec.
Qed.
Local Hint Resolve weaken_subtykn.

(** ** Lack of Transitivity

    Despite that Kernel D#<sub>&lt;:</sub># has no transitivity, it is still possible to show that
    Kernel D#<sub>&lt;:</sub># is transitivity on [⊤] and [⊥].
 *)

Fixpoint bnd_layer (T : typ) (Ts : list typ) : typ :=
  match Ts with
  | nil => T
  | cons T' Ts =>
    typ_bnd T' (bnd_layer T Ts)
  end.

Lemma trans_on_top : forall L G T,
    [ L ] G ⊢k typ_top <⦂ T ->
    forall S,
      [ L ] G ⊢k S <⦂ T
with layered_top_trans : forall L G T l U,
    [ L ] G ⊢k T <⦂ bnd_layer (typ_bnd typ_top U) l ->
    forall S,
      [ L ] G ⊢k T <⦂ bnd_layer (typ_bnd S U) l.
Proof.
  - clear trans_on_top.
    dep induction on subtykn; eroutine.
    econstructor; eauto.
    apply layered_top_trans with (l := nil).
    trivial.

  - clear layered_top_trans.
    intros. gen S. dependent induction H; intros; eauto.
    1-5:induction l; eroutine.

    econstructor; eauto.
    specialize (IHsubtykn (cons typ_bot l) U eq_refl).
    simpl in IHsubtykn. auto.
Qed.
Local Hint Resolve trans_on_top.

Lemma trans_on_bot : forall L G T,
    [ L ] G ⊢k T <⦂ typ_bot ->
    forall U,
      [ L ] G ⊢k T <⦂ U
with layered_bot_trans : forall L G T l S,
    [ L ] G ⊢k T <⦂ bnd_layer (typ_bnd S typ_bot) l ->
    forall U,
      [ L ] G ⊢k T <⦂ bnd_layer (typ_bnd S U) l.
Proof.
  - clear trans_on_bot.
    dep induction on subtykn; eroutine.
    econstructor; eauto.
    apply layered_bot_trans with (l := nil).
    trivial.

  - clear layered_bot_trans.
    intros. gen U.
    dependent induction H; intros; eauto.
    1-5:induction l; eroutine.

    econstructor; eauto.
    specialize (IHsubtykn (cons typ_bot l) S eq_refl).
    simpl in IHsubtykn. auto.
Qed.
Local Hint Resolve trans_on_bot.

(** ** Soundness and Completeness of Step Subtyping w.r.t. Kernel D#<sub>&lt;:</sub># *)

(** Recall that there is an alternative definition of [Exposure], which is used here
    to serve as an intermediate setup to show the soundness theorem of kernel D#<sub>&lt;:</sub>#.
 *)
Theorem exposure'_to_subtykn : forall G S U,
    exposure' G S U ->
    forall L U',
      [ L ] G ⊢k U <⦂ U' ->
      [ L ] G ⊢k S <⦂ U'.
Proof.
  induction on exposure'.
  1,2,4:eroutine.
  routine.
  econstructor; try eassumption.
  eauto.
Qed.  

(** *** The soundness theorem *)
Theorem stp_subty_to_subtykn : forall L G S U,
    [ L ] G ⊢s S <⦂ U ->
    [ L ] G ⊢k S <⦂ U.
Proof.
  induction on stp_subty; routine.
  - destruct H; eauto.
    + econstructor. eauto.
      apply exposure_weakening with (G' := G2 ++ x ~ T) in H.
      rewrite app_assoc in H.
      apply exposure_to_exposure' in H.
      eapply exposure'_to_subtykn; eauto.
    + econstructor; eauto.
      apply exposure_weakening with (G' := G2 ++ x ~ T) in H.
      rewrite app_assoc in H.
      apply exposure_to_exposure' in H.
      eapply exposure'_to_subtykn; eauto.      
      
  - destruct H; eauto.
    + econstructor. eauto.
      apply exposure_weakening with (G' := G2 ++ x ~ T) in H.
      rewrite app_assoc in H.
      apply exposure_to_exposure' in H.
      eapply exposure'_to_subtykn; eauto.
    + econstructor; eauto.
      apply exposure_weakening with (G' := G2 ++ x ~ T) in H.
      rewrite app_assoc in H.
      apply exposure_to_exposure' in H.
      eapply exposure'_to_subtykn; eauto.      

  - eauto.
Qed.

(** *** The completeness theorem

    Similar to [Exposure], there is also a need to define alternative definitions of
[Upcast] and [Downcast]. *)
Inductive upcast_e' : env -> avar -> typ -> Prop :=
| ue_top : forall G x,
    upcast_e' G x typ_top
| ue_bot : forall G x T,
    binds x T G ->
    exposure' G T typ_bot ->
    upcast_e' G (avar_f x) typ_bot
| ue_bnd : forall G x T L U,
    binds x T G ->
    exposure' G T (typ_bnd L U) ->
    upcast_e' G (avar_f x) U.
Local Hint Constructors upcast_e'.

Inductive downcast_e' : env -> avar -> typ -> Prop :=
| de_bot : forall G x,
    downcast_e' G x typ_bot
| de_top : forall G x T,
    binds x T G ->
    exposure' G T typ_bot ->
    downcast_e' G (avar_f x) typ_top
| de_bnd : forall G x T L U,
    binds x T G ->
    exposure' G T (typ_bnd L U) ->
    downcast_e' G (avar_f x) L.
Local Hint Constructors downcast_e'.

(** Finally, we define a definition of step subtyping where the contexts are not
truncated. This is an intermediate setup to show completeness. *)
Inductive stp_subty' : vars -> env -> typ -> typ -> Prop :=
| ss'_top : forall L G T, stp_subty' L G T typ_top
| ss'_bot : forall L G T, stp_subty' L G typ_bot T
| ss'_sel_refl : forall L G x,
    stp_subty' L G (typ_sel x) (typ_sel x)
| ss'_sel_left : forall L G x T U,
    upcast_e' G x T ->
    stp_subty' L G T U ->
    stp_subty' L G (typ_sel x) U
| ss'_sel_right : forall L G x T U,
    downcast_e' G x T ->
    stp_subty' L G U T ->
    stp_subty' L G U (typ_sel x)
| ss'_bnd : forall L G S1 U1 S2 U2,
    stp_subty' L G S2 S1 ->
    stp_subty' L G U1 U2 ->
    stp_subty' L G (typ_bnd S1 U1) (typ_bnd S2 U2)
| ss'_all : forall L G T U1 U2 x,
    x `notin` fv G `union` fv T
      `union` fv U1 `union` fv U2 `union` L ->
    stp_subty' (L  `union` singleton x `union` fv T)
              (x ~ T ++ G) (open x U1) (open x U2) ->
    stp_subty' L G (typ_all T U1) (typ_all T U2).
Local Hint Constructors stp_subty' exposure'.

Program Fixpoint stp_subty'_refl T {measure (typ_struct_measure T)}
  : forall L G,
    stp_subty' L G T T := _.
Next Obligation.
  destruct T; eroutine.
  - pick_fresh x.
    econstructor.
    + instantiate (1 := x).
      auto.
    + apply stp_subty'_refl.
      rewrite open_typ_same_measure.
      lia.
  - constructor.
    all:apply stp_subty'_refl; lia.
Qed.
Local Hint Resolve stp_subty'_refl.

(** The following definition is a special definition of kernel D#<sub>&lt;:</sub>#, where the steps of
derivations are accounted for as part of the judgments. Let us call this form
"step-enriched". This is necessary as we (mistakenly) define judgments in [Prop], which
cannot be eliminated into [Set] or [Type]. The steps of derivations are eventually
used in the well-foundness induction in the completeness theorem.  *)
Inductive subtykn' : vars -> env -> typ -> typ -> nat -> Prop :=
| snf'_refl : forall L G x, subtykn' L G (typ_sel x) (typ_sel x) 1
| snf'_top : forall L G T, subtykn' L G T typ_top 1
| snf'_bot : forall L G T, subtykn' L G typ_bot T 1
| snf'_bnd : forall L G S T1 T2 U n1 n2,
    subtykn' L G S T1 n1 -> subtykn' L G T2 U n2 ->
    subtykn' L G (typ_bnd T1 T2) (typ_bnd S U) (1 + n1 + n2)
| snf'_all : forall L G T U1 U2 x n,
    x `notin` union (fv G)
      (union (fv T) (union (fv U1) (union (fv U2) L))) ->
    subtykn' (union L (union (singleton x) (fv T)))
            (x ~ T ++ G) (open x U1) (open x U2) n ->
    subtykn' L G (typ_all T U1) (typ_all T U2) (1 + n)
| snf'_sel1 : forall L G x T S n,
    binds x T G ->
    subtykn' L G T (typ_bnd S typ_top) n ->
    subtykn' L G S (typ_sel $ avar_f x) (1 + n)
| snf'_sel2 : forall L G x T U n,
    binds x T G ->
    subtykn' L G T (typ_bnd typ_bot U) n ->
    subtykn' L G (typ_sel $ avar_f x) U (1 + n).
Hint Constructors subtykn'.
Notation "[ L , n ] G ⊢k S <⦂ U" := (subtykn' L G S U n) (at level 70).

Lemma subtykn_to_subtykn' : forall L G S U,
    [ L ] G ⊢k S <⦂ U ->
    exists n, [ L , n ] G ⊢k S <⦂ U.
Proof.
  induction on subtykn; eroutine.
Qed.

Lemma subtykn'_to_subtykn : forall L G S U n,
    [ L , n ] G ⊢k S <⦂ U ->
    [ L ] G ⊢k S <⦂ U.
Proof.
  induction on subtykn'; eroutine.
Qed.

(** It is quite straightforward to show the equivalence of kernel D#<sub>&lt;:</sub># and this
"step-enriched" definition of kernel D#<sub>&lt;:</sub>#. *)
Lemma subtykn_equiv_subtykn' : forall L G S U,
    [ L ] G ⊢k S <⦂ U <->
    exists n, [ L , n ] G ⊢k S <⦂ U.
Proof.
  split; auto using subtykn_to_subtykn'.
  intros. tidy_up.
  eauto using subtykn'_to_subtykn.
Qed.

Local Hint Extern 1 (_ <= _) => lia.

(** This is the auxiliary lemma of completeness theorem. *)
Program Fixpoint subtykn'_conversions n {measure n} : forall L G S U,
    [ L , n ] G ⊢k S <⦂ U ->
    stp_subty' L G S U /\
    (forall T1 T2,
        U = typ_bnd T1 T2 ->
        exists S', exposure' G S S' /\
              (S' = typ_bot \/
               exists T1' T2' n',
                 S' = typ_bnd T1' T2' /\
                 stp_subty' L G T1 T1' /\
                 ([ L , n' ] G ⊢k T2' <⦂ T2) /\ n' <= n))
  := _.
Next Obligation.
  split; intros.
  - induction H; routine.
    + eapply ss'_all with x; auto.
    + clear IHsubtykn'.
      apply subtykn'_conversions in H0; auto.
      tidy_up.
      specialize (H1 _ _ eq_refl).
      tidy_up; eauto 10.
    + clear IHsubtykn'.
      apply subtykn'_conversions in H0; auto.
      tidy_up.
      specialize (H1 _ _ eq_refl).
      tidy_up; eauto.

      apply subtykn'_conversions in H8; auto.
      tidy_up. eauto.

  - destruct H; subst; progressive_inversions.
    + eroutine at 14.
    + eexists. split; [apply ex_stop; auto |].
      right. repeat eexists; try eassumption; auto.
      eapply subtykn'_conversions; try eassumption.
      lia.
    + apply subtykn'_conversions in H1; try lia.
      tidy_up.
      specialize (H1 _ _ eq_refl).
      tidy_up; eauto.

      apply subtykn'_conversions in H8; try lia.
      tidy_up.
      specialize (H6 _ _ eq_refl).
      tidy_up; eauto 14.
Qed.

(** At this step, we show that step subtyping is complete w.r.t. kernel D#<sub>&lt;:</sub># if
contexts are not truncated. The final step is to show that step subtyping performs the
same with and without the contexts truncated. *)
Theorem subtykn_to_stp_subty' : forall L G S U,
    [ L ] G ⊢k S <⦂ U ->
    stp_subty' L G S U.
Proof.
  intros. 
  rewrite subtykn_equiv_subtykn' in *.
  tidy_up.
  eapply subtykn'_conversions.
  eauto.
Qed.

Local Hint Constructors stp_subty upcast_e downcast_e.
Local Hint Resolve exposure'_to_exposure.
  
Local Ltac wf_env :=
  lazymatch goal with
  | H : wf_env (_ ++ _) |- _ => apply wf_deapp in H; invert H; subst
  end.

Lemma upcast_e'_to_upcast_e : forall G x T,
    upcast_e' G x T ->
    wf_env G ->
    upcast_e G x T.
Proof.
  destr on upcast_e'; eroutine.
  all:apply binds_app in H; tidy_up;
    pose proof H1; wf_env.

  - eapply uce_bot.
    apply exposure_strengthening with (G2 := (H ++ x ~ T));
      try rewrite app_assoc in *; eauto.  
  - eapply uce_bnd.
    apply exposure_strengthening with (G2 := (H ++ x ~ T));
      try rewrite app_assoc in *; eauto.
Qed.

Lemma downcast_e'_to_downcast_e : forall G x T,
    downcast_e' G x T ->
    wf_env G ->
    downcast_e G x T.
Proof.
  destr on downcast_e'; eroutine.
  all:apply binds_app in H; tidy_up;
    pose proof H1; wf_env.

  - eapply dce_top.
    apply exposure_strengthening with (G2 := (H ++ x ~ T));
      try rewrite app_assoc in *; eauto.  
  - eapply dce_bnd.
    apply exposure_strengthening with (G2 := (H ++ x ~ T));
      try rewrite app_assoc in *; eauto.
Qed.

Local Hint Resolve upcast_e_preserves_wf upcast_e_preserves_lc upcast_e'_to_upcast_e.
Local Hint Resolve downcast_e_preserves_wf
      downcast_e_preserves_lc downcast_e'_to_downcast_e.

Lemma stp_subty'_to_stp_subty : forall L G S U,
    stp_subty' L G S U ->
    wf_env G ->
    fv S [<=] dom G -> lc S ->
    fv U [<=] dom G -> lc U ->
    [ L ] G ⊢s S <⦂ U.
Proof.
  induction on stp_subty'; intros; eauto.
  - econstructor.
    + apply upcast_e'_to_upcast_e; eassumption.
    + progressive_inversions.
      apply IHstp_subty'; eauto.
  - econstructor.
    + apply downcast_e'_to_downcast_e; eassumption.
    + progressive_inversions.
      apply IHstp_subty'; eauto.
  - progressive_inversions. simpl in *.
    fold_cls. auto 10.
  - progressive_inversions. simpl in *.
    invert H2; subst. fold_cls.
    apply ss_all with x; auto.
    apply IHstp_subty'.
    all:try apply open_lc_typ; trivial.
    + constructor; auto.
    + pose proof (fv_open_typ U1 x 0).
      etransitivity; [ eassumption |].
      set solve.
    + pose proof (fv_open_typ U2 x 0).
      etransitivity; [ eassumption |].
      set solve.
Qed.

(** The completeness theorem is thus established. *)
Theorem subtykn_to_stp_subty : forall L G S U,
    [ L ] G ⊢k S <⦂ U ->
    wf_env G ->
    fv S [<=] dom G -> lc S ->
    fv U [<=] dom G -> lc U ->
    [ L ] G ⊢s S <⦂ U.
Proof.
  intros.
  auto using subtykn_to_stp_subty', stp_subty'_to_stp_subty.
Qed.

Theorem subtykn_equiv_stp_subty : forall L G S U,
    wf_env G ->
    fv S [<=] dom G -> lc S ->
    fv U [<=] dom G -> lc U ->
    [ L ] G ⊢k S <⦂ U <->
    [ L ] G ⊢s S <⦂ U.
Proof.
  split; auto using subtykn_to_stp_subty, stp_subty_to_subtykn.
Qed.
