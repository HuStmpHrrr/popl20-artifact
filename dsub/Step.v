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
Require Import Misc.
Require Import ListRelations.

From Equations Require Export Equations.

Require Import Stareat.

(** * Definitions Related to Step Subtyping
    
    Step subtyping was originally developed in Nieto17 and it is the first
 formalization of algorithmic subtyping of D#<sub>D<:lt;:</sub>.
  *)


(** ** Definition of [Exposure] *)
Reserved Notation "G ⊢ S ⇑ U" (at level 90).
Inductive exposure : env -> typ -> typ -> Prop :=
(** [T is not a path] #<br>#
    [―――――――――――――] Exp-Stop #<br>#
    [G ⊢ T ⇑ T] *)
| exp_stop : forall G T,
    ~is_sel T ->
    G ⊢ T ⇑ T
(** [―――――――――] Exp-Top* #<br>#
    [G ⊢ T ⇑ ⊤] *)
| exp_top : forall G T,
    G ⊢ T ⇑ typ_top
(** [G1 ⊢ T ⇑ ⊥] #<br>#
    [―――――――――――――――――――――――――] Exp-Bot #<br>#
    [G1 ; x : T ; G2 ⊢ x.A ⇑ ⊥] *)
| exp_bot : forall G1 G2 T x,
    G1 ⊢ T ⇑ typ_bot ->
    G2 ++ x ~ T ++ G1 ⊢ typ_sel (avar_f x) ⇑ typ_bot
(** [G1 ⊢ T ⇑ {A : S .. U}] #<br>#
    [G1 ⊢ U ⇑ U'] #<br>#
    [――――――――――――――――――――――――――] Exp-Bnd #<br>#
    [G1 ; x : T ; G2 ⊢ x.A ⇑ U'] *)
| exp_bnd : forall G1 G2 T x L U U',
    G1 ⊢ T ⇑ (typ_bnd L U) ->
    G1 ⊢ U ⇑ U' ->
    G2 ++ x ~ T ++ G1 ⊢ typ_sel (avar_f x) ⇑ U'
where "G ⊢ S ⇑ U" := (exposure G S U).
Local Hint Constructors exposure.
Local Hint Constructors revealing.

Lemma prefix_wf_env : forall G1 G2,
    prefix G1 G2 ->
    wf_env G2 ->
    wf_env G1.
Proof. induction on @prefix; routine. Qed.
  
Local Ltac wf_env :=
  lazymatch goal with
  | H : wf_env (_ ++ _) |- _ => apply wf_deapp in H; invert H; subst
  end.      

Section RevealingSubsumesExposure.
  
  Hint Resolve prefix_nil pf_refl prefix_trans.
  
  Lemma revealing_gives_prefix : forall G T G' U,
    G ⊢ T ⤊ G' ⊢! U ->
    prefix G' G.
  Proof.
    induction on revealing; routine.
    eauto using prefix_deapp, prefix_decons.
  Qed.

  Hint Constructors revealing.

  Lemma revealing_sel_weakening : forall G x D U,
      G ⊢ typ_sel (avar_f x) ⤊ D ⊢! U ->
      forall G',
        G' ++ G ⊢ typ_sel (avar_f x) ⤊ D ⊢! U.
  Proof.
    dep induction on revealing;
      try solve [routine]; intros.
    - simpl in *. contradiction.
    - reassoc 4 with 2 3. eauto.
    - reassoc 4 with 2 3. eauto.
  Qed.

  Lemma revealing_sel_weakening_prefix : forall G x D U,
      G ⊢ typ_sel (avar_f x) ⤊ D ⊢! U ->
      forall G',
        prefix G G' ->
        G' ⊢ typ_sel (avar_f x) ⤊ D ⊢! U.
  Proof.
    intros. apply prefix_to_app in H0.
    tidy_up. apply revealing_sel_weakening.
    trivial.
  Qed.
  
  Theorem exposure_to_revealing_gen : forall G S U,
      G ⊢ S ⇑ U ->
      wf_env G ->
      forall G',
        prefix G' G ->
        fv S [<=] dom G' ->
      exists D,
        G' ⊢ S ⤊ D ⊢! U.
  Proof.
    induction on exposure; try solve [eroutine]; intros.
    - pose proof (wf_uniq H).
      wf_env.
      edestruct IHexposure; trivial.
      eexists. simpl in *.
      eapply in_prefix_binds with (l := G') in H3; set solve.
      progressive_destructions.
      subst. eauto.
    - pose proof (wf_uniq H).
      wf_env.
      edestruct IHexposure1; trivial.
      eapply in_prefix_binds with (l := G') in H2; set solve.
      progressive_destructions.
      subst.
      edestruct (IHexposure2 H8 x0); trivial.
      + eapply revealing_gives_prefix. eassumption.
      + apply revealing_preserves_wf in H3; trivial.
        progressive_destructions.
        simpl in *. set solve.
      + eauto.
  Qed.

  Theorem exposure_to_revealing : forall G S U,
      G ⊢ S ⇑ U ->
      wf_env G ->
      fv S [<=] dom G ->
      exists D,
        G ⊢ S ⤊ D ⊢! U.
  Proof.
    intros. eapply exposure_to_revealing_gen; eauto.
  Qed.
  
End RevealingSubsumesExposure.

(** ** Definition of [Upcast]

    This is the [Exposure] version of [Upcast]. Since [Upcast] and [Downcast] are induced
  directly from [Exposure]/[Revealing], their names are directly inherited.
 *)
Reserved Notation "G ⊢ S ↗! U" (at level 90).
Inductive upcast_e : env -> avar -> typ -> Prop :=
(** [―――――――――――] Uc-Top* #<br>#
    [G ⊢ x.A ↗! ⊤] *)
| uce_top : forall G x,
    G ⊢ x ↗! typ_top
(** [G1 ⊢ T ⇑ ⊥] #<br>#
    [―――――――――――――――――――――――――] Uc-Bot #<br>#
    [G1 ; x : T ; G2 ⊢ x.A ↗! ⊥] *)
| uce_bot : forall G1 G2 x T ,
    G1 ⊢ T ⇑ typ_bot ->
    G2 ++ x ~ T ++ G1 ⊢ avar_f x ↗! typ_bot
(** [G1 ⊢ T ⇑ {A : L .. U}] #<br>#
    [―――――――――――――――――――――――――] Uc-Bnd #<br>#
    [G1 ; x : T ; G2 ⊢ x.A ↗! U] *)
| uce_bnd : forall G1 G2 x T L U,
    G1 ⊢ T ⇑ typ_bnd L U ->
    G2 ++ x ~ T ++ G1 ⊢ avar_f x ↗! U
where "G ⊢ S ↗! U" := (upcast_e G S U).
Local Hint Constructors upcast_e.

(** ** Definition of [Downcast] *)
Reserved Notation "G ⊢ S ↘! U" (at level 90).
Inductive downcast_e : env -> avar -> typ -> Prop :=
(** [―――――――――――] Dc-Bot* #<br>#
    [G ⊢ x.A ↘! ⊥] *)
| dce_bot : forall G x,
    G ⊢ x ↘! typ_bot
(** [G1 ⊢ T ⇑ ⊥] #<br>#
    [―――――――――――――――――――――――――] Dc-Top #<br>#
    [G1 ; x : T ; G2 ⊢ x.A ↘! ⊤] *)
| dce_top : forall G1 G2 x T,
    G1 ⊢ T ⇑ typ_bot ->
    G2 ++ x ~ T ++ G1 ⊢ avar_f x ↘! typ_top
(** [G1 ⊢ T ⤊ {A : L .. U}] #<br>#
    [―――――――――――――――――――――――――] Dc-Bnd #<br>#
    [G1 ; x : T ; G2 ⊢ x.A ↘! L] *)
| dce_bnd : forall G1 G2 x T L U,
    G1 ⊢ T ⇑ (typ_bnd L U) ->
    G2 ++ x ~ T ++ G1 ⊢ avar_f x ↘! L
where "G ⊢ S ↘! U" := (downcast_e G S U).
Local Hint Constructors downcast_e.

(** ** Definition of Step Subtyping *)

Reserved Notation "[ L ] G ⊢s S <⦂ U" (at level 70).
Inductive stp_subty : vars -> env -> typ -> typ -> Prop :=
(** [―――――――――――] S-Top #<br>#
    [G ⊢s T <: ⊤] *)
| ss_top : forall L G T,
    [ L ] G ⊢s T <⦂ typ_top
(** [―――――――――――] S-Top #<br>#
    [G ⊢s ⊥ <: T] *)
| ss_bot : forall L G T,
    [ L ] G ⊢s typ_bot <⦂ T
(** [―――――――――――――――] S-VRefl #<br>#
    [G ⊢s x.A <: x.A] *)
| ss_sel_refl : forall L G x,
    [ L ] G ⊢s typ_sel x <⦂ typ_sel x
(** [G ⊢ x.A ↗! T] #<br>#
    [G ⊢s T <: U] #<br>#
    [―――――――――――――] S-Sel2 #<br>#
    [G ⊢s x.A <: U] *)
| ss_sel_left : forall L G x T U,
    G ⊢ x ↗! T ->
    [ L ] G ⊢s T <⦂ U ->
    [ L ] G ⊢s typ_sel x <⦂ U
(** [G ⊢ x.A ↘! T] #<br>#
    [G ⊢s U <: T] #<br>#
    [―――――――――――――] S-Sel1 #<br>#
    [G ⊢s U <: x.A] *)
| ss_sel_right : forall L G x T U,
    G ⊢ x ↘! T ->
    [ L ] G ⊢s U <⦂ T ->
    [ L ] G ⊢s U <⦂ typ_sel x
(** [G ⊢ S2 <: S1] #<br>#
    [G ⊢s U1 <: U2] #<br>#
    [―――――――――――――――――――――――――――――――――――――] S-Bnd #<br>#
    [G ⊢s {A : S1 .. U1} <: {A : S2 .. U2}] *)
| ss_bnd : forall L G S1 U1 S2 U2,
    [ L ] G ⊢s S2 <⦂ S1 ->
    [ L ] G ⊢s U1 <⦂ U2 ->
    [ L ] G ⊢s typ_bnd S1 U1 <⦂ typ_bnd S2 U2
(** [G ; x : S ⊢s U1 <: U2] #<br>#
    [―――――――――――――――――――――――――――――] S-All #<br>#
    [G ⊢s ∀(x : S)U1 <: ∀(x : S)U2] *)
| ss_all : forall L G T U1 U2 x,
    x `notin` fv G `union` fv T
      `union` fv U1 `union` fv U2 `union` L ->
    [ L  `union` singleton x `union` fv T ]
      x ~ T ++ G ⊢s open x U1 <⦂ open x U2 ->
    [ L ] G ⊢s typ_all T U1 <⦂ typ_all T U2
where "[ L ] G ⊢s S <⦂ U" := (stp_subty L G S U).

Lemma ope_list_fv_env_subset : forall (G1 G2 : env),
    ope_list G1 G2 ->
    fv G1 [<=] fv G2.
Proof.
  induction on @ope_list; set solve.
  all:destruct_conjs; simpl in *; fsetdec.
Qed.

Lemma exposure_strengthening : forall G1 G2 S U,
    G2 ++ G1 ⊢ S ⇑ U ->
    wf_env (G2 ++ G1) ->
    fv S [<=] dom G1 ->
    G1 ⊢ S ⇑ U.
Proof.
  dep induction on exposure;
    intros; auto.
  - gen G2. induction H0; intros; simpl in *.
    + subst. wf_env. apply exp_bot; eauto.
    + progressive_inversions. specialize (IHlist H8).
      destruct G2; progressive_inversions; eauto.
      exfalso. apply H6. rewrite fv_union. simpl.
      set solve.

  - gen G2. induction H0; intros; simpl in *.
    + subst. wf_env. eapply exp_bnd; eauto.
    + progressive_inversions. specialize (IHlist H7).
      destruct G2; progressive_inversions; eauto.
      exfalso. apply H5. rewrite fv_union. simpl.
      set solve.
Qed.

Lemma exposure_preserves_wf : forall G S U,
    G ⊢ S ⇑ U ->
    wf_env G ->
    fv S [<=] dom G ->
    fv U [<=] dom G.
Proof.
  induction on exposure; intros; set solve.
  wf_env. specialize (IHexposure1 H6 H5).
  simpl in IHexposure1.
  rewrite union_conj in IHexposure1. destruct_conjs.
  specialize (IHexposure2 H6 H2).
  set solve.
Qed.

Lemma exposure_preserves_lc : forall G S U,
    G ⊢ S ⇑ U ->
    wf_env G ->
    lc S ->
    lc U.
Proof.
  induction on exposure; eroutine.
  wf_env. specialize (IHexposure1 H7 H8).
  routine.
Qed.

Lemma upcast_e_preserves_wf : forall G x T,
    G ⊢ x ↗! T ->
    wf_env G ->
    fv x [<=] dom G ->
    fv T [<=] dom G.
Proof.
  destr on upcast_e; intros; set solve.
  wf_env. apply exposure_preserves_wf in H; auto.
  set solve.
Qed.  

Lemma upcast_e_preserves_lc : forall G x T,
    G ⊢ x ↗! T ->
    wf_env G ->
    lc x ->
    lc T.
Proof.
  destr on upcast_e; routine.
  wf_env. apply exposure_preserves_lc in H; auto.
  routine.
Qed.

Lemma downcast_e_preserves_wf : forall G x T,
    G ⊢ x ↘! T ->
    wf_env G ->
    fv x [<=] dom G ->
    fv T [<=] dom G.
Proof.
  destr on downcast_e; intros; set solve.
  wf_env. apply exposure_preserves_wf in H; auto.
  set solve.
Qed.  

Lemma downcast_e_preserves_lc : forall G x T,
    G ⊢ x ↘! T ->
    wf_env G ->
    lc x ->
    lc T.
Proof.
  destr on downcast_e; routine.
  wf_env. apply exposure_preserves_lc in H; auto.
  routine.
Qed.


Section BisubtyStronger.
  Hint Constructors upcast downcast stareat ope_list.
  Hint Resolve exposure_to_revealing.
  
  Lemma upcast_e_to_upcast : forall G x T,
      G ⊢ x ↗! T ->
      wf_env G ->
      exists G',
        G ⊢ x ↗ G' ⊢! T.
  Proof.
    destruct 1; intros; eauto; wf_env.
    - apply exposure_to_revealing in H; trivial.
      destruct_conjs.
      eexists. eapply uc_bot. eassumption.
    - apply exposure_to_revealing in H; trivial.
      destruct_conjs.
      eexists. eapply uc_bnd. eassumption.
  Qed.

  Lemma downcast_e_to_downcast : forall G x T,
      G ⊢ x ↘! T ->
      wf_env G ->
      exists G',
        G ⊢ x ↘ G' ⊢! T.
  Proof.
    destruct 1; intros; eauto; wf_env.
    - apply exposure_to_revealing in H; trivial.
      destruct_conjs.
      eexists. eapply dc_top. eassumption.
    - apply exposure_to_revealing in H; trivial.
      destruct_conjs.
      eexists. eapply dc_bnd. eassumption.
  Qed.    

  Hint Resolve ope_list_to_nil.
  Hint Extern 1 (_ [<=] _) => simpl in *; set solve.

  Ltac destruct_env_by x G :=
    let H := fresh "H" in
    assert (H : x `in` dom G) by set solve;
    apply in_to_binds in H; destruct_conjs;
    match goal with
    | H' : binds x _ G |- _ =>
      apply binds_app in H'; destruct_conjs;
      subst G
    end.
  
  Lemma revealing_strengthening : forall G T D U,
      G ⊢ T ⤊ D ⊢! U ->
      forall G',
        ope_list G' G ->
        wf_env G' -> wf_env G ->
        fv T [<=] dom G' ->
        exists D',
          (G' ⊢ T ⤊ D' ⊢! U) /\ ope_list D' D.
  Proof.
    induction on revealing; intros; eauto.
    - destruct_env_by x G'.
      pose proof (wf_uniq H1).
      pose proof (ope_list_witness_uniq H H7).
      destruct_conjs. subst H4.
      wf_env. clear H1. wf_env.
      destruct (IHrevealing H6); trivial.
      destruct_conjs.
      exists nil. eauto.
    - destruct_env_by x G'.
      pose proof (wf_uniq H1).
      pose proof (ope_list_witness_uniq H H6).
      destruct_conjs. subst H3.
      wf_env. clear H1. wf_env.

      destruct (IHrevealing1 H5); trivial.
      destruct_conjs.

      apply revealing_preserves_wf in H3_; trivial.
      destruct_conjs.
      pose proof H1.
      apply revealing_preserves_wf in H1; trivial.
      destruct_conjs.
      
      destruct (IHrevealing2 x0); auto. destruct_conjs.
      exists x1. split; eauto.
  Qed.

  Lemma upcast_strengthening : forall G x D T,
      G ⊢ x ↗ D ⊢! T ->
      forall G',
        ope_list G' G ->
        wf_env G' -> wf_env G ->
        fv x [<=] dom G' ->
        exists D', (G' ⊢ x ↗ D' ⊢! T) /\ ope_list D' D.
  Proof.
    destruct 1; intros; eauto.
    - exists nil. split; auto.
      destruct_env_by x G'.
      pose proof (wf_uniq H2).
      pose proof (ope_list_witness_uniq H0 H7).
      destruct_conjs. subst.

      wf_env. clear H2. wf_env.
      apply revealing_strengthening with (G' := H6) in H; trivial.
      destruct_conjs. eauto.
    - destruct_env_by x G'.
      pose proof (wf_uniq H2).
      pose proof (ope_list_witness_uniq H0 H7).
      destruct_conjs. subst.
      wf_env. clear H2. wf_env.
      apply revealing_strengthening with (G' := H6) in H; trivial.
      destruct_conjs. eauto.
  Qed.

  Lemma downcast_strengthening : forall G x D T,
      G ⊢ x ↘ D ⊢! T ->
      forall G',
        ope_list G' G ->
        wf_env G' -> wf_env G ->
        fv x [<=] dom G' ->
        exists D', (G' ⊢ x ↘ D' ⊢! T) /\ ope_list D' D.
  Proof.
    destruct 1; intros; eauto.
    - exists nil. split; auto.
      destruct_env_by x G'.
      pose proof (wf_uniq H2).
      pose proof (ope_list_witness_uniq H0 H7).
      destruct_conjs. subst.

      wf_env. clear H2. wf_env.
      apply revealing_strengthening with (G' := H6) in H; trivial.
      destruct_conjs. eauto.
    - destruct_env_by x G'.
      pose proof (wf_uniq H2).
      pose proof (ope_list_witness_uniq H0 H7).
      destruct_conjs. subst.
      wf_env. clear H2. wf_env.
      apply revealing_strengthening with (G' := H6) in H; trivial.
      destruct_conjs. eauto.
  Qed.

  Hint Resolve ope_list_trans ope_list_refl.
  Hint Extern 2 (lc_at _ _) => progressive_inversions; assumption.
  Hint Extern 2 (lc_typ_at _ _) => progressive_inversions; assumption.
  
  Theorem stareat_strengthening : forall L G T U D,
      [ L ] G >> T <⦂ U << D ->
      forall G' D',
        ope_list G' G ->
        wf_env G -> wf_env G' ->
        fv T [<=] dom G' -> lc T ->
        ope_list D' D ->
        wf_env D -> wf_env D' ->
        fv U [<=] dom D' -> lc U ->
        [ L ] G' >> T <⦂ U << D'.
  Proof.
    induction on stareat; intros; eauto.
    - pose proof H.
      apply upcast_strengthening with (G' := G') in H; trivial.
      destruct_conjs.
      eapply sa_sel_left; eauto.
      simpl in H3.
      pose proof (upcast_preserves_wf H12 H2 H3).
      destruct_conjs.
      pose proof (ope_list_dom H0).
      pose proof (upcast_preserves_wf H11 H1 ltac:(fsetdec)).
      destruct_conjs.
      apply IHstareat; trivial.

    - pose proof H.
      apply downcast_strengthening with (G' := D') in H; trivial.
      destruct_conjs.
      eapply sa_sel_right; eauto.
      simpl in H9.
      pose proof (downcast_preserves_wf H12 H8 H9).
      destruct_conjs.
      pose proof (ope_list_dom H6).
      pose proof (downcast_preserves_wf H11 H7 ltac:(fsetdec)).
      destruct_conjs.
      apply IHstareat; trivial.
      
    - pose proof (ope_list_dom H0).
      pose proof (ope_list_dom H5).
      pose proof (ope_list_fv_env_subset H0).
      pose proof (ope_list_fv_env_subset H5).

      apply sa_all with (x := x).
      + fsetdec.
      + apply IHstareat1; trivial.
        all:simpl in *; set solve.
      + apply IHstareat2; simpl in *;
          lazymatch goal with
          | |- ope_list _ _ => auto
          | |- lc_typ_at _ _ =>
            apply open_lc_typ; auto
          | |- wf_env _ =>
            constructor; trivial;
              [ simpl in *; fsetdec | simpl in *; fsetdec | auto ]
          | _ => idtac
          end.
        * pose proof (fv_open_typ U1 x 0).
          simpl in *.
          etransitivity; [ eassumption |].
          clear H. fsetdec.
        * pose proof (fv_open_typ U2 x 0).
          simpl in *.
          etransitivity; [ eassumption |].
          clear H. fsetdec.
  Qed.

  Hint Resolve prefix_nil prefix_trans prefix_app.
  Hint Constructors prefix.
  
  Lemma upcast_gives_prefix : forall G T D U,
      G ⊢ T ↗ D ⊢! U ->
      prefix D G.
  Proof.
    destruct 1; auto.
    etransitivity.
    - eapply revealing_gives_prefix. eauto.
    - eauto.
  Qed.

  Lemma downcast_gives_prefix : forall G T D U,
      G ⊢ T ↘ D ⊢! U ->
      prefix D G.
  Proof.
    destruct 1; auto.
    etransitivity.
    - eapply revealing_gives_prefix. eauto.
    - eauto.
  Qed.

  Theorem stp_subty_to_stareat : forall L G T U,
      [ L ] G ⊢s T <⦂ U ->
      wf_env G ->
      fv T [<=] dom G -> lc T ->
      fv U [<=] dom G -> lc U ->
      [ L ] G >> T <⦂ U << G.
  Proof.
    induction on stp_subty; intros; auto.
    - apply upcast_e_to_upcast in H; trivial.
      destruct_conjs. econstructor.
      + eassumption.
      + pose proof (upcast_preserves_wf H6 H0 ltac:(simpl in *; fsetdec)).
        destruct_conjs.
        pose proof (upcast_gives_prefix H6).
        pose proof (prefix_is_ope_list H11).
        pose proof (ope_list_dom H12).
        
        specialize (IHstp_subty ltac:(trivial) ltac:(fsetdec)
                                ltac:(trivial) ltac:(trivial) ltac:(trivial)).
        eapply stareat_strengthening; eauto.

    - apply downcast_e_to_downcast in H; trivial.
      destruct_conjs. econstructor.
      + eassumption.
      + pose proof (downcast_preserves_wf H6 H0 ltac:(simpl in *; fsetdec)).
        destruct_conjs.
        pose proof (downcast_gives_prefix H6).
        pose proof (prefix_is_ope_list H11).
        pose proof (ope_list_dom H12).
        
        specialize (IHstp_subty ltac:(trivial) ltac:(trivial)
                                ltac:(trivial) ltac:(fsetdec) ltac:(trivial)).
        eapply stareat_strengthening; eauto.

    - apply sa_all with (x := x).
      + fsetdec.
      + apply stareat_refl.
      + invert H2; invert H5; subst.
        apply IHstp_subty; simpl in *;
          lazymatch goal with
          | |- ope_list _ _ => auto
          | |- lc_typ_at _ _ =>
            apply open_lc_typ; auto
          | |- wf_env _ =>
            constructor; trivial;
              [ simpl in *; fsetdec | auto ]
          | _ => idtac
          end.
        * pose proof (fv_open_typ U1 x 0).
          simpl in *.
          etransitivity; [ eassumption |].
          clear H. fsetdec.
        * pose proof (fv_open_typ U2 x 0).
          simpl in *.
          etransitivity; [ eassumption |].
          clear H. fsetdec.
  Qed.

End BisubtyStronger.

Theorem exposure_weakening : forall G S U,
    G ⊢ S ⇑ U ->
    forall G',
      G' ++ G ⊢ S ⇑ U.
Proof.
  induction on exposure; intros; auto.
  all:reassoc 4 with 2; eauto.
Qed.

Lemma revealing_to_exposure : forall G S G' U,
    G ⊢ S ⤊ G' ⊢! U ->
    G ⊢ S ⇑ U.
Proof.
  induction on revealing; routine.
  - constructor; trivial.
  - econstructor; eauto.
    apply revealing_gives_prefix in H3_0.
    apply prefix_to_app in H3_0.
    apply revealing_gives_prefix in H3_.
    apply prefix_to_app in H3_.
    tidy_up.
    apply exposure_weakening.
    trivial.
Qed.

(** ** An Alternative Definition of [Exposure]
    
    In this definition of [Exposure], contexts are not truncated in the premises. It
 turns out that two definitions are equivalent. This definition is a convenient setup 
 to show the completeness theorem w.r.t. Kernel D#<sub>D<:lt;:</sub>.
 *)
Section EquivalentRepr.
  
  Inductive exposure' : env -> typ -> typ -> Prop :=
  | ex_stop : forall G T,
      ~is_sel T ->
      exposure' G T T
  | ex_top : forall G T,
      exposure' G T typ_top
  | ex_bot : forall G T x,
      binds x T G ->
      exposure' G T typ_bot ->
      exposure' G (typ_sel (avar_f x)) typ_bot
  | ex_bnd : forall G T x L U U',
      binds x T G ->
      exposure' G T (typ_bnd L U) ->
      exposure' G U U' ->
      exposure' G (typ_sel (avar_f x)) U'.
  Local Hint Constructors exposure'.

  Theorem exposure'_weakening : forall G S U,
      exposure' G S U ->
      forall G',
        exposure' (G' ++ G) S U.
  Proof.
    induction on exposure'; intros; eauto.
  Qed.

  Local Hint Resolve binds_weaken.
  
  Theorem exposure'_weakening_gen : forall G1 G2 S U,
      exposure' (G1 ++ G2) S U ->
      forall G,
        exposure' (G1 ++ G ++ G2) S U.
  Proof.
    dep induction on exposure'; intros; eauto.
  Qed.
  
  Local Hint Resolve exposure_weakening exposure'_weakening.

  Lemma exposure_to_exposure' : forall G S U,
      G ⊢ S ⇑ U ->
      exposure' G S U.
  Proof.
    induction on exposure; auto.
    - eapply ex_bot. auto.
      reassoc 3 with 2. auto.
    - eapply ex_bnd; auto.
      all:reassoc 3 with 2; eauto.
  Qed.  

  Lemma exposure'_to_exposure : forall G S U,
      exposure' G S U ->
      wf_env G ->
      G ⊢ S ⇑ U.
  Proof.
    induction on exposure'; intros; auto.
    - pose proof H.
      apply binds_app in H. tidy_up.
      eapply exp_bot.
      specialize (IHexposure' H0).
      apply exposure_strengthening with (G2 := H ++ x ~ T).
      all:try rewrite app_assoc in *; auto.
      wf_env. trivial.
    - pose proof H.
      apply binds_app in H. tidy_up.
      specialize (IHexposure'1 H0).
      specialize (IHexposure'2 H0).
      rewrite cons_app_one, <- app_assoc in IHexposure'1.
      apply exposure_strengthening in IHexposure'1; auto.
      eapply exp_bnd; eauto.

      apply exposure_strengthening with (G2 := H ++ x ~ T).
      all:try rewrite app_assoc in *; eauto.
      + wf_env.
        apply exposure_preserves_wf in IHexposure'1; eauto.
        set solve.
      + wf_env; trivial.
  Qed.

  Lemma exposure'_equiv_exposure : forall G S U,
      wf_env G ->
      G ⊢ S ⇑ U <->
      exposure' G S U.
  Proof.
    intros.
    split; auto using exposure'_to_exposure, exposure_to_exposure'.
  Qed. 
  
End EquivalentRepr.

(** ** A Formalization of Termination of Step Subtyping
    
    One can see from the setup here to understand why it is necessary to easy the
 proof of termination. The complexity can quickly become unmanageable if the setup is
 not fundamentally simplified. 

 There are two technical details worth mentioning:
 - The measure is in fact _partial_. That means the measure in fact cannot be directly
   implemented in type theory. The treatment here is set "impossible" cases to be 0,
   and use logical predicate to avoid those cases. However, this induces way more
   technical setup.
 - Since variables are represented by local nameless representation with cofinite
   quantification, the measure needs to carry two contexts, the one with names and one
   for de Bruijn indices. Thus, lemmas are required to connect both contexts.
 *)
Section MeasuresAndFacts.
  
  Local Notation denv := (list typ).

  Definition denv_fv (D : denv) : atoms :=
    fold_right (fun T fvs => fvs \u fv T) {} D.
  Arguments denv_fv D/.

  Instance FvDenv : HasFv denv := { fv := denv_fv }.

  Definition denv_measure (D : denv) : nat :=
    total $ List.map typ_struct_measure D.
  Arguments denv_measure D/.
  
  Definition wf_measure G D T : nat :=
    env_measure G + denv_measure D + typ_struct_measure T.
  Arguments wf_measure G D T/.

  (** The measure is computed from a regular context AND a de Bruijn context, represented by [D]. *)
  Equations wf_search_impl (G : env) (D : denv) (T : typ) : nat by wf (wf_measure G D T) lt :=
    {
      wf_search_impl G D typ_top := 1;
      wf_search_impl G D typ_bot := 1;
      wf_search_impl G nil (typ_sel (avar_b n)) := 0;
      wf_search_impl G (T' :: D) (typ_sel (avar_b 0)) := 1 + wf_search_impl G D T';
      wf_search_impl G (T' :: D) (typ_sel (avar_b (S n))) := wf_search_impl G D (typ_sel (avar_b n));
      wf_search_impl nil D (typ_sel (avar_f y)) := 0;
      wf_search_impl ((x, T') :: G) D (typ_sel (avar_f y))
        with x == y => {
      | in_left => 1 + wf_search_impl G nil T';
      | in_right => wf_search_impl G D (typ_sel (avar_f y))
      };
      wf_search_impl G D (typ_bnd T U) :=
        1 + Nat.max (wf_search_impl G D T) (wf_search_impl G D U);
      wf_search_impl G D (typ_all T U) :=
        1 + wf_search_impl G (T :: D) U
    }.
  Next Obligation.
    autorewrite with measures. lia.
  Qed.
  Next Obligation.
    autorewrite with measures.
    pose proof (typ_struct_measure_ge_1 T'). lia.
  Qed.
  Next Obligation. lia. Qed.
  Next Obligation.
    pose proof (typ_struct_measure_ge_1 T'). lia.
  Qed.
  Next Obligation.
    autorewrite with measures.
    pose proof (typ_struct_measure_ge_1 T'). lia.
  Qed.
  Next Obligation.
    autorewrite with measures.
    pose proof (typ_struct_measure_ge_1 T'). lia.
  Qed.
  Next Obligation. lia. Qed.
  Next Obligation. lia. Qed.
  Next Obligation. lia. Qed.

  Definition wf_search G T : nat := wf_search_impl G nil T.
  
  Local Ltac mass_discharge :=
    simpl; trivial; try eassumption; try lia; set solve; try fsetdec.
  
  Fixpoint wf_search_fv G (D : denv) v : nat :=
    match G with
    | nil => 0
    | cons (v', T') G' =>
      if v' == v
      then 1 + wf_search_impl G' nil T'
      else wf_search_fv G' D v
    end.
  
  Lemma fv_search_equiv : forall G D v,
      wf_search_fv G D v = wf_search_impl G D (typ_sel $ avar_f v).
  Proof.
    intros.
    funelim (wf_search_impl G D (typ_sel (avar_f v)));
      progressive_inversions;
      simpl in *; auto.
    all: try rewrite Heq; trivial.
  Qed.

  Lemma fv_ignores_D : forall G D v,
      wf_search_fv G D v = wf_search_fv G nil v.
  Proof. induction G; routine. Qed.
  
  Fixpoint wf_search_bv G D n : nat :=
    match D with
    | nil => 0
    | cons T' D' =>
      match n with
      | O => 1 + wf_search_impl G D' T'
      | S n' => wf_search_bv G D' n'
      end
    end.

  Lemma bv_search_equiv : forall G D n,
      wf_search_bv G D n = wf_search_impl G D (typ_sel $ avar_b n).
  Proof.
    intros.
    funelim (wf_search_impl G D (typ_sel $ avar_b n));
      progressive_inversions;
      simpl in *; auto.
  Qed.

  Lemma bv_search_idx : forall G D1 D2 T,
      wf_search_bv G (D1 ++ [T] ++ D2) (length D1) =
      1 + wf_search_impl G D2 T.
  Proof.
    induction D1; intros; simpl.
    - trivial.
    - simpl in IHD1. rewrite IHD1. trivial.
  Qed.
  
  Definition wf_search_avar G D v : nat :=
    match v with
    | avar_b n => wf_search_bv G D n
    | avar_f v => wf_search_fv G D v
    end.

  Lemma avar_search_equiv : forall G D v,
      wf_search_avar G D v = wf_search_impl G D (typ_sel v).
  Proof.
    intros. destruct v; simpl.
    - apply bv_search_equiv.
    - apply fv_search_equiv.
  Qed.
  
  Lemma wf_search_fv_weaken : forall G1 G2 D v,
      wf_env (G1 ++ G2) ->
      v `in` dom G2 ->
      wf_search_fv G2 D v = wf_search_fv (G1 ++ G2) D v.
  Proof.
    induction G1; intros; trivial.
    destruct_conjs. simpl. destruct_eq.
    - exfalso. eapply wf_var_in; mass_discharge.
    - apply IHG1; routine.
  Qed.

  Definition wf_weaken_measure (D : denv) (T : typ) : nat :=
    denv_measure D + typ_struct_measure T.
  Arguments wf_weaken_measure D T/.

  Program Fixpoint wf_search_weaken_gen D T {measure (wf_weaken_measure D T)} :
    forall G1 G2,
      wf_env (G1 ++ G2) ->
      fv T [<=] dom G2 ->
      fv D [<=] dom G2 ->
      wf_search_impl G2 D T = wf_search_impl (G1 ++ G2) D T := _.
  Next Obligation.
    destruct T; simp wf_search_impl.
    - destruct a.
      + destruct D; destruct n; simp wf_search_impl.
        * simpl in H1.
          erewrite wf_search_weaken_gen; mass_discharge.
        * pose proof (typ_struct_measure_ge_1 t).
          erewrite wf_search_weaken_gen; mass_discharge.
      + assert (a `in` dom G2) by set solve.
        pose proof (wf_search_fv_weaken G1 G2 D H H2).
        do 2 rewrite fv_search_equiv in H3.
        simp wf_search_impl in H3.
    - simpl in *. erewrite wf_search_weaken_gen; simpl; auto.
      + lia.
      + set solve.
    - simpl in *. erewrite wf_search_weaken_gen; simpl; eauto; try lia.
      erewrite wf_search_weaken_gen with (G2 := G2); simpl; eauto.
      lia.
  Qed.
            
  Theorem wf_search_weaken : forall G1 G2 T,
      wf_env (G1 ++ G2) ->
      fv T [<=] dom G2 ->
      wf_search G2 T = wf_search (G1 ++ G2) T.
  Proof.
    intros. apply wf_search_weaken_gen; mass_discharge.
  Qed.

  Lemma wf_lookup_lt : forall G1 G2 x T,
      wf_env (G1 ++ x ~ T ++ G2) ->
      fv T [<=] dom G2 ->
      wf_search G2 T <
      wf_search (G1 ++ x ~ T ++ G2) (typ_sel $ avar_f x).
  Proof.
    intros. rewrite <- wf_search_weaken; set solve.
    unfold wf_search.
    simp wf_search_impl.
    destruct (x == x); try congruence.
    simpl. lia.
  Qed.      
  
  Inductive incr_lc : list typ -> Prop :=
  | lc_nil : incr_lc nil
  | lc_cons : forall T D, lc_at (length D) T -> incr_lc D -> incr_lc (T :: D).
  Hint Constructors incr_lc.

  Fixpoint open_rec_D v (D : denv) :=
    match D with
    | nil => nil
    | cons T D' => open_rec (length D') v T :: open_rec_D v D'
    end.

  Lemma wf_search_impl_avar_f_eq : forall G D x T y,
      wf_search_impl (x ~ T ++ G) D (typ_sel (avar_f y)) =
      match x == y with
      | in_left => 1 + wf_search_impl G nil T
      | in_right => wf_search_impl G D (typ_sel (avar_f y))
      end.
  Proof.
    intros. destruct D; simp wf_search_impl; destruct_eq; simpl; auto.
  Qed.

  (** This theorem connects the regular context with the de Bruijn context. It states
  that pushing a type into the de Bruijn context, is the same as pushing into the
  regular context, with the de Bruijn context and the type opened by that type.

  This theorem heavily relies on the well-formedness predicate, which is an indirect
  indicator of the measure function being partial.
   *)
  Program Fixpoint wf_open_shift_gen D U {measure (wf_weaken_measure D U)} :
    forall G n T x,
      wf_env G ->
      fv U [<=] dom G ->
      fv D [<=] dom G ->
      incr_lc (D ++ [T]) ->
      length D = n ->
      x `notin` fv G \u fv D \u fv T \u fv U ->
      lc_at (S n) U ->
      wf_search_impl G (D ++ [T]) U =
      wf_search_impl (x ~ T ++ G) (open_rec_D x D) (open_rec n x U) := _.
  Next Obligation.
    destruct U; simpl; simp wf_search_impl.
    - destruct a; simpl.
      + destruct_eq.
        * rewrite <- bv_search_equiv.
          rewrite bv_search_idx.
          rewrite wf_search_impl_avar_f_eq.
          destruct_eq; trivial.
        * progressive_inversions.
          assert (n < length D) by lia.
          destruct D; simpl in *.
          -- lia.
          -- progressive_inversions.
             rewrite app_length in *.
             rewrite Nat.add_comm in H10. trivial.
             destruct n; simp wf_search_impl.
             ++ erewrite wf_open_shift_gen; eroutine.
             ++ pose proof (typ_struct_measure_ge_1 t).
                erewrite wf_open_shift_gen; eroutine.
                repeat constructor.
                lia.
      + rewrite wf_search_impl_avar_f_eq.
        destruct_eq.
        * simpl in *. solve_notin.
        * do 2 rewrite <- fv_search_equiv.
          rewrite fv_ignores_D.
          rewrite fv_ignores_D with (D := _ _ D).
          trivial.
    - change (U1 :: D ++ [T]) with ((U1 :: D) ++ [T]).
      simpl in H0.
      erewrite wf_open_shift_gen; try solve [eroutine].
      + simpl. set solve.
      + simpl. constructor; routine.
        rewrite app_length in *.
        rewrite Nat.add_comm. trivial.
    - do 2 try erewrite wf_open_shift_gen; try solve [eroutine].
  Qed.

  (** This lemma effectively eliminates the need of the de Bruijn context. *)
  Lemma wf_open_shift : forall G T U x,
      wf_env G ->
      fv T [<=] dom G ->
      fv U [<=] dom G ->
      x `notin` fv G \u fv T \u fv U ->
      lc T ->
      lc_at 1 U ->
      wf_search_impl G [T] U =
      wf_search_impl (x ~ T ++ G) nil (open x U).
  Proof.
    intros. eapply wf_open_shift_gen with (D := nil); trivial.
    all:progressive_destructions; simpl in *; mass_discharge.
    repeat constructor. trivial.
  Qed.

End MeasuresAndFacts.
Arguments wf_search G T/.

(** ** Proofs of Step Subtyping Being Algorithmic

    - step subtyping is sound, and
    - step subtyping terminates.
 *)
Section Algorithmic.
  
  Lemma exposure_sound : forall G S U,
    G ⊢ S ⇑ U ->
    G ⊢ S <⦂ U.
  Proof.
    induction on exposure; routine.
    - pose proof (binds_for_sure G2 G1 x T).
      eapply st_sel2. instantiate (1 := typ_top).
      simpl_env.
      eapply ty_sub; eauto using weaken_subty.
    - pose proof (binds_for_sure G2 G1 x T).
      eapply st_sel2. instantiate (1 := L).
      simpl_env.
      eapply ty_sub; eauto using weaken_subty.
  Qed.
  
  Theorem stp_subty_sound : forall L G S U,
      [ L ] G ⊢s S <⦂ U ->
      uniq G ->
      G ⊢ S <⦂ U.
  Proof.
    induction on stp_subty; routine.
    - destruct H; eauto using exposure_sound.
      apply exposure_sound in H.
      pose proof (binds_for_sure G2 G1 x T).
      eapply st_trans; [| apply IHstp_subty]; trivial.
      eapply st_sel2. instantiate (1 := L0).
      eapply ty_sub; eauto using weaken_subty.
    - destruct H; eauto.
      + pose proof (binds_for_sure G2 G1 x T).
        eapply st_sel1. instantiate (1 := typ_top).
        eapply ty_sub; eauto using exposure_sound, weaken_subty.
      + apply exposure_sound in H.
        pose proof (binds_for_sure G2 G1 x T).
        eapply st_trans; [apply IHstp_subty |]; trivial.
        eapply st_sel1. instantiate (1 := U0).
        eapply ty_sub; eauto using weaken_subty.
    - eapply st_all; auto.
      assert (x `notin` fv G) by (simpl; auto).
      cofinite. apply open_subst_subty with (x := x); trivial.
      + repeat (apply notin_union_3; auto).
      + auto.
      + apply IHstp_subty.
        auto.
  Qed.

  (** This is a predicate which asserts the termination of step subtyping. *)
  Inductive stp_subty_termination : forall L G S U,
      [ L ] G ⊢s S <⦂ U -> Prop :=
  | sst_top : forall L G T, stp_subty_termination (ss_top L G T)
  | sst_bot : forall L G T, stp_subty_termination (ss_bot L G T)
  | sst_sel_refl : forall L G x, stp_subty_termination (ss_sel_refl L G x)
  | sst_sel_left : forall L G x T U
                     (Uc : upcast_e G x T)
                     (Rec : stp_subty L G T U),
      wf_search G T + wf_search G U < wf_search G (typ_sel x) + wf_search G U ->
      stp_subty_termination (ss_sel_left Uc Rec)
  | sst_sel_right : forall L G x T U
                      (Dc : downcast_e G x T)
                      (Rec : stp_subty L G U T),
      wf_search G U + wf_search G T < wf_search G U + wf_search G (typ_sel x) ->
      stp_subty_termination (ss_sel_right Dc Rec)
  | sst_bnd : forall L G S1 U1 S2 U2
                (Rec1 : stp_subty L G S2 S1)
                (Rec2 : stp_subty L G U1 U2),
      wf_search G S2 + wf_search G S1 < wf_search G (typ_bnd S1 U1) + wf_search G (typ_bnd S2 U2) ->
      wf_search G U1 + wf_search G U2 < wf_search G (typ_bnd S1 U1) + wf_search G (typ_bnd S2 U2) ->
      stp_subty_termination (ss_bnd Rec1 Rec2)
  | sst_all : forall L G T U1 U2 x
                (Rec : stp_subty (union L (union (singleton x) (fv T))) (x ~ T ++ G) (open x U1) (open x U2))
                (Ni : x `notin` union (fv G) (union (fv T) (union (fv U1) (union (fv U2) L)))),
      wf_search (x ~ T ++ G) (open x U1) +
      wf_search (x ~ T ++ G) (open x U2) <
      wf_search G (typ_all T U1) + wf_search G (typ_all T U2) ->
      stp_subty_termination (ss_all U1 U2 Ni Rec).
  Hint Constructors stp_subty_termination.

  Lemma wf_search_wf_ge_1 : forall G T,
      wf_env G ->
      fv T [<=] dom G -> lc T ->
      wf_search G T >= 1.
  Proof.
    destruct T; intros; simpl; simp wf_search_impl; auto; try lia.

    destruct a; progressive_inversions.
    induction G; simpl in *.
    - tidy_up. specialize (H0 a ltac:(auto)).
      rewrite empty_iff in H0. contradiction.
    - progressive_inversions.
      rewrite wf_search_impl_avar_f_eq.
      destruct_eq.
      + rewrite wf_fv_is_dom in NotInTac by trivial.
        lia.
      + assert (singleton a [<=] dom G) by fsetdec.
        auto.
  Qed.

  Lemma wf_search_lookup : forall G1 G2 D x T,
      uniq (G2 ++ x ~ T ++ G1) ->
      wf_search_impl (G2 ++ x ~ T ++ G1) D (typ_sel (avar_f x))
      = 1 + wf_search_impl G1 nil T.
  Proof.
    intros. rewrite <- fv_search_equiv.
    induction G2; intros; destruct_conjs; simpl.
    - destruct_eq; auto.
    - destruct_eq.
      + simpl in *. solve_uniq.
      + rewrite IHG2; routine.
  Qed.
  
  Lemma exposure_measure_decrease : forall G S U,
      G ⊢ S ⇑ U ->
      wf_env G -> fv S [<=] dom G -> lc S ->
      wf_search G S >= wf_search G U.
  Proof.
    induction on exposure; simpl; simp wf_search_impl; intros; auto.
    - apply wf_search_wf_ge_1; auto.
    - simpl in *; simp  wf_search_impl in *.
      rewrite wf_search_lookup; try lia.
      auto using wf_uniq.
    - pose proof H. apply wf_deapp in H.
      progressive_inversions.
      rec_pose IHexposure1 Hrec1; auto.
      rec_pose (exposure_preserves_wf H2_) Wf; auto.
      rec_pose (exposure_preserves_lc H2_) Lc; auto.
      progressive_inversions. simpl in *.
      rec_pose IHexposure2 Hrec2; auto.
      simp wf_search_impl in Hrec1.
      rewrite wf_search_lookup; try lia; auto using wf_uniq.
      rec_pose (exposure_preserves_wf H2_0) Wf'; auto.
      change (wf_search_impl ?G nil ?T) with (wf_search G T).
      rewrite <- wf_search_weaken; set solve.
      simpl_env.
      rewrite <- wf_search_weaken; set solve.
      simpl. lia.
  Qed.

  Lemma upcast_e_measure_decrease : forall G x T,
      G ⊢ x ↗! T ->
      wf_env G -> fv x [<=] dom G -> lc x ->
      wf_search G (typ_sel x) > wf_search G T.
  Proof.
    destr on upcast_e; intros; simpl; simp wf_search_impl; try lia.
    - destruct x; progressive_inversions.
      simpl in H0. assert (a `in` dom G) by fsetdec.
      apply in_witness in H2.
      destruct_conjs. subst.
      rewrite wf_search_lookup; auto using wf_uniq.
      apply wf_deapp in H. progressive_inversions.
      pose proof (wf_search_wf_ge_1 H10 H9 H11).
      simpl in *. lia.
    - rewrite wf_search_lookup; auto using wf_uniq.
      apply wf_deapp in H0. progressive_inversions.
      pose proof (wf_search_wf_ge_1 H8 H7 H9).
      simpl in *. lia.
    - pose proof H0. apply wf_deapp in H0.
      progressive_inversions.
      rec_pose (exposure_preserves_wf H) Wf; auto.
      rec_pose (exposure_preserves_lc H) Lc; auto.
      simpl in *.
      apply exposure_measure_decrease in H; trivial.
      rewrite wf_search_lookup; auto using wf_uniq.
      simpl_env.
      change (wf_search_impl ?G nil ?T) with (wf_search G T).
      do 2 (rewrite <- wf_search_weaken; set solve).
      simpl in *. simp wf_search_impl in *.
      lia.
  Qed.

  Lemma downcast_e_measure_decrease : forall G x T,
      G ⊢ x ↘! T ->
      wf_env G -> fv x [<=] dom G -> lc x ->
      wf_search G (typ_sel x) > wf_search G T.
  Proof.
    destr on downcast_e; intros; simpl; simp wf_search_impl; try lia.
    - destruct x; progressive_inversions.
      simpl in H0. assert (a `in` dom G) by fsetdec.
      apply in_witness in H2.
      destruct_conjs. subst.
      rewrite wf_search_lookup; auto using wf_uniq.
      apply wf_deapp in H. progressive_inversions.
      pose proof (wf_search_wf_ge_1 H10 H9 H11).
      simpl in *. lia.
    - rewrite wf_search_lookup; auto using wf_uniq.
      apply wf_deapp in H0. progressive_inversions.
      pose proof (wf_search_wf_ge_1 H8 H7 H9).
      simpl in *. lia.
    - pose proof H0. apply wf_deapp in H0.
      progressive_inversions.
      rec_pose (exposure_preserves_wf H) Wf; auto.
      rec_pose (exposure_preserves_lc H) Lc; auto.
      simpl in *.
      apply exposure_measure_decrease in H; trivial.
      rewrite wf_search_lookup; auto using wf_uniq.
      simpl_env.
      change (wf_search_impl ?G nil ?T) with (wf_search G T).
      do 2 (rewrite <- wf_search_weaken; set solve).
      simpl in *. simp wf_search_impl in *.
      lia.
  Qed.

  Fixpoint stp_subty_terminates L G S U (SU : [ L ] G ⊢s S <⦂ U)
           {struct SU} :
    wf_env G ->
    fv S [<=] dom G -> lc S ->
    fv U [<=] dom G -> lc U ->
    stp_subty_termination SU.
  Proof.
    intros; destruct SU; constructor;
      simpl; simp wf_search_impl; try lia.
    - apply upcast_e_measure_decrease in u; auto.
      simpl in *. lia. routine.
    - apply downcast_e_measure_decrease in d; auto.
      simpl in *. lia. routine.
    - simpl in *. progressive_inversions.
      invert H1. subst.
      do 2 (rewrite <- wf_open_shift; auto).
      change (<[?T]>) with [T].
      lia.
  Qed.

End Algorithmic.
