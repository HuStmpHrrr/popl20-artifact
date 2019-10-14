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
Require Import Misc.
Require Import OperationProperties.
Require Import StructuralProperties.
Require Import OpeSub.
Require Import ListRelations.

(** * Definition and Properties of (Strong) Kernel F#<sub>&lt;:</sub># *)

(** ** Kernel F#<sub>&lt;:</sub># *)
Reserved Notation "[ L ] G ⊢k T '<⦂' U" (at level 70).
Inductive k_subty : atoms -> env -> typ -> typ -> Prop :=
(** [―――――――――――] F-K-Top #<br>#
    [G ⊢k T <: ⊤] *)
| k_top : forall L G T,
    [ L ] G ⊢k T <⦂ typ_top
(** [―――――――――――] F-K-TVRefl #<br>#
    [G ⊢k X <: X] *)
| k_tvrefl : forall L G x,
    [ L ] G ⊢k typ_var x <⦂ typ_var x
(** [X <: T ∈ G] #<br>#
    [G ⊢k T <: U] #<br>#
    [―――――――――――] F-K-TVar #<br>#
    [G ⊢k X <: U] *)
| k_tvar : forall L G x T U,
    binds x T G ->
    [ L ] G ⊢k T <⦂ U ->
    [ L ] G ⊢k typ_var (avar_f x) <⦂ U
(** [G ⊢k S2 <: S1] #<br>#
    [G ⊢k U1 <: U2] #<br>#
    [―――――――――――――――――――――――] F-K-Fun #<br>#
    [G ⊢k S1 ⟶ U1 <: S2 ⟶ U2] *)
| k_fun : forall L G S1 U1 S2 U2,
    [ L ] G ⊢k S2 <⦂ S1 ->
    [ L ] G ⊢k U1 <⦂ U2 ->
    [ L ] G ⊢k typ_fun S1 U1 <⦂ typ_fun S2 U2
(** [G ; X <: S ⊢k U1 <: U2] #<br>#
    [――――――――――――――――――――――――――――――――――――] F-K-All #<br>#
    [G ⊢ (∀ X <: S. U1) <: (∀ X <: S. U2)] *)
| k_all : forall L x G T U1 U2 ,
    x `notin` fv G `union` fv T
      `union` fv U1 `union` fv U2  `union` L ->
    [ L `union` singleton x `union` fv T ]
      x ~ T ++ G ⊢k open x U1 <⦂ open x U2 ->
    [ L ] G ⊢k typ_all T U1 <⦂ typ_all T U2
where "[ L ] G ⊢k T '<⦂' U" := (k_subty L G T U)%type.
Hint Constructors k_subty.

(** ** Strong Kernel F#<sub>&lt;:</sub># *)
Reserved Notation "[ L ] G1 ⊢k T '<⦂' U ⊣ G2" (at level 70).
Inductive sk_subty : atoms -> env -> typ -> typ -> env -> Prop :=
(** [―――――――――――――――――] F-SK-Top #<br>#
    [G1 ⊢k T <: ⊤ ⊣ G2] *)
| sk_top : forall L G1 T G2,
    [ L ] G1 ⊢k T <⦂ typ_top ⊣ G2
(** [―――――――――――――――――] F-SK-TVRefl #<br>#
    [G1 ⊢k X <: X ⊣ G2] *)
| sk_tvrefl : forall L G1 x G2,
    [ L ] G1 ⊢k typ_var x <⦂ typ_var x ⊣ G2
(** [X <: T ∈ G1] #<br>#
    [G1 ⊢k T <: U ⊣ G2] #<br>#
    [―――――――――――――――――] F-SK-TVRefl #<br>#
    [G1 ⊢k X <: U ⊣ G2] *)
| sk_tvar : forall L G1 x T U G2,
    binds x T G1 ->
    [ L ] G1 ⊢k T <⦂ U ⊣ G2 ->
    [ L ] G1 ⊢k typ_var (avar_f x) <⦂ U ⊣ G2
(** [G1 ⊢k S1 >: S2 ⊣ G2] #<br>#
    [G1 ⊢k U1 <: U2 ⊣ G2] #<br>#
    [―――――――――――――――――――――――――――――] F-SK-Fun #<br>#
    [G1 ⊢k S1 ⟶ U1 <: S2 ⟶ U2 ⊣ G2] *)
| sk_fun : forall L G1 S1 U1 S2 U2 G2,
    [ L ] G2 ⊢k S2 <⦂ S1 ⊣ G1 ->
    [ L ] G1 ⊢k U1 <⦂ U2 ⊣ G2 ->
    [ L ] G1 ⊢k typ_fun S1 U1 <⦂ typ_fun S2 U2 ⊣ G2
(** [G1 ⊢k S1 >: S2 ⊣ G2] #<br>#
    [G1 ; X <: S1 ⊢k U1 <: U2 ⊣ G2 ; X <: S2] #<br>#
    [―――――――――――――――――――――――――――――――――――――――――――――] F-SK-All #<br>#
    [G1 ⊢k (∀ X <: S1. U1) <: (∀ X <: S2. U2) ⊣ G2] *)
| sk_all : forall L x G1 S1 U1 S2 U2 G2,
    x `notin` fv G1 `union` fv S1 `union` fv S2
      `union` fv U1 `union` fv U2 `union` fv G2 `union` L ->
    [ L ] G2 ⊢k S2 <⦂ S1 ⊣ G1 ->
    [ L `union` singleton x `union` fv S2 ]
      x ~ S1 ++ G1 ⊢k open x U1 <⦂ open x U2 ⊣ x ~ S2 ++ G2 ->
    [ L ] G1 ⊢k typ_all S1 U1 <⦂ typ_all S2 U2 ⊣ G2
where "[ L ] G1 ⊢k T '<⦂' U ⊣ G2" := (sk_subty L G1 T U G2)%type.
Hint Constructors sk_subty.

(** step-enriched strong kernel F#<sub>&lt;:</sub># *)
Reserved Notation "[ L , n ] G1 ⊢k T '<⦂' U ⊣ G2" (at level 70).
Inductive sk_subty' : atoms -> env -> typ -> typ -> env -> nat -> Prop :=
| sk_top' : forall L G1 T G2, [ L , 1 ] G1 ⊢k T <⦂ typ_top ⊣ G2
| sk_tvrefl' : forall L G1 x G2, [ L , 1 ] G1 ⊢k typ_var x <⦂ typ_var x ⊣ G2
| sk_tvar' : forall L G1 x T U G2 n,
    binds x T G1 ->
    [ L , n ] G1 ⊢k T <⦂ U ⊣ G2 ->
    [ L , S n ] G1 ⊢k typ_var (avar_f x) <⦂ U ⊣ G2
| sk_fun' : forall L G1 S1 U1 S2 U2 G2 n1 n2,
    [ L , n1 ] G2 ⊢k S2 <⦂ S1 ⊣ G1 ->
    [ L , n2 ] G1 ⊢k U1 <⦂ U2 ⊣ G2 ->
    [ L , S (n1 + n2) ] G1 ⊢k typ_fun S1 U1 <⦂ typ_fun S2 U2 ⊣ G2
| sk_all' : forall L x G1 S1 U1 S2 U2 G2 n1 n2,
    x `notin` fv G1 `union` fv S1 `union` fv S2
      `union` fv U1 `union` fv U2 `union` fv G2 `union` L ->
    [ L , n1 ] G2 ⊢k S2 <⦂ S1 ⊣ G1 ->
    [ L `union` singleton x `union` fv S2 , n2 ]
      x ~ S1 ++ G1 ⊢k open x U1 <⦂ open x U2 ⊣ x ~ S2 ++ G2 ->
    [ L , S (n1 + n2) ] G1 ⊢k typ_all S1 U1 <⦂ typ_all S2 U2 ⊣ G2
where "[ L , n ] G1 ⊢k T '<⦂' U ⊣ G2" := (sk_subty' L G1 T U G2 n)%type.
Hint Constructors sk_subty'.

Lemma sk_subty_to_sk_subty' : forall L G1 S U G2,
    [ L ] G1 ⊢k S <⦂ U ⊣ G2 ->
    exists n, [ L , n ] G1 ⊢k S <⦂ U ⊣ G2.
Proof. induction on sk_subty; eroutine. Qed.

Lemma sk_subty'_to_sk_subty : forall L n G1 S U G2,
    [ L , n ] G1 ⊢k S <⦂ U ⊣ G2 ->
    [ L ] G1 ⊢k S <⦂ U ⊣ G2.
Proof. induction on sk_subty'; eroutine. Qed.

Lemma sk_subty_equiv_sk_subty' : forall L G1 S U G2,
    [ L ] G1 ⊢k S <⦂ U ⊣ G2 <->
    exists n, [ L , n ] G1 ⊢k S <⦂ U ⊣ G2.
Proof.
  split.
  - apply sk_subty_to_sk_subty'.
  - intros. tidy_up.
    eapply sk_subty'_to_sk_subty.
    eauto.
Qed.

Local Hint Extern 1 (_ <= _) => autorewrite with measures; simpl; lia.

(** Strong kernel F#<sub>&lt;:</sub># is reflexive. *)
Section Reflexivity.
  
  Program Fixpoint sksub_refl T {measure (typ_struct_measure T)} :
    forall L G1 G2,
      [ L ] G1 ⊢k T <⦂ T ⊣ G2 := _.
  Next Obligation.
    destruct T; routine at 3.
    pick_fresh x. eauto.
  Qed.

End Reflexivity.
Hint Resolve sksub_refl.

(** Strong kernel F#<sub>&lt;:</sub># is sound w.r.t. F#<sub>&lt;:</sub># normal form *)
Section Soundness.

  Theorem sk_subty_to_subty : forall L G1 S U G2,
    [L] G1 ⊢k S <⦂ U ⊣ G2 ->
    forall G,
      fv G [<=] L ->
      uniq G ->
      G ⊆<⦂ G1 ->
      G ⊆<⦂ G2 ->
      G ⊢F S <⦂ U.
  Proof.
    induction on sk_subty; try solve [routine at 3]; intros.
    - rec_pose (IHsk_subty G) Hrec; auto.
      eapply ope_narrow_var in H; eauto.
      destruct_conjs. eauto.
    - eapply st_all; eauto.
      cofinite.
      apply open_subst_subty with (x := x); auto; clear Fr.
      + fsetdec.
      + apply IHsk_subty2.
        * set solve.
        * constructor; trivial.
          simpl in *. fsetdec.
        * simpl; auto using os_keep.
        * simpl; auto using os_keep.
  Qed.

  Theorem sk_subty_sound : forall L G S U,
    [L] G ⊢k S <⦂ U ⊣ G ->
    fv G [<=] L ->
    uniq G ->
    G ⊢F S <⦂ U.
  Proof.
    intros. eapply sk_subty_to_subty; eauto.
    all:apply ope_sub_refl.
  Qed.
    
End Soundness.

(** Strong kernel F#<sub>&lt;:</sub># admits weakening. *)
Section Weakening.
  
  Theorem sksub_weaken_gen : forall L' G1 G2 S U G3 G4,
    [ L' ] G1 ++ G2 ⊢k S <⦂ U ⊣ G3 ++ G4 ->
    forall G G' L,
      L `union` fv G' `union` fv G [<=] L' ->
      [ L ] G1 ++ G ++ G2 ⊢k S <⦂ U ⊣ G3 ++ G' ++ G4.
  Proof.
    dep induction on sk_subty; intros; try solve [routine].
    - specialize (IHsk_subty _ _ _ _ ltac:(reflexivity) ltac:(reflexivity) _ _ _ H2).
      eauto using binds_weaken.
    - set solve.
    - econstructor.
      + instantiate (1 := x).
        autorewrite with meta_ext in *.
        destruct_conjs. rewrite <- in_subset_singleton in *.
        fsetdec.
      + set solve.
      + specialize (IHsk_subty2 (x ~ S1 ++ H0) _ (x ~ S2 ++ H4) _ ltac:(reflexivity) ltac:(reflexivity)).
        set solve.
  Qed.

  Theorem sksub_weaken_l : forall L' L G G' S U G2,
    [ L' ] G ⊢k S <⦂ U ⊣ G2 ->
      L `union` fv G' [<=] L' ->
      [ L ] G' ++ G ⊢k S <⦂ U ⊣ G2.
  Proof.
    intros.
    eapply sksub_weaken_gen with (G1:=nil) (G3:=nil) (G':=nil);
      eauto.
    simpl in *. fsetdec.
  Qed.
    
End Weakening.

(** Kernel F#<sub>&lt;:</sub># is weaker than strong kernel F#<sub>&lt;:</sub># *)
Theorem k_subty_to_sk_subty : forall L G S U,
    k_subty L G S U ->
    [ L ] G ⊢k S <⦂ U ⊣ G.
Proof. induction on k_subty; eroutine. Qed.

(** ** Stare-at subtyping for F#<sub>&lt;:</sub>#
 
  The difference between stare-at subtyping and strong kernel is little in F#<sub>&lt;:</sub>#,
  because type variables are not as rich as in D<:. This phenomenon is captured by the
  concept of "higher-dimensional subtyping" in my thesis.  
*)
Reserved Notation "[ L ] G1 >> T '<⦂' U << G2" (at level 70).
Inductive stareat : atoms -> env -> typ -> typ -> env -> Prop :=
| sa_top : forall L G1 T G2, [ L ] G1 >> T <⦂ typ_top << G2
| sa_tvrefl : forall L G1 x G2, [ L ] G1 >> typ_var x <⦂ typ_var x << G2
| sa_tvar : forall L G G' x T U G2,
    [ L ] G >> T <⦂ U << G2 ->
    [ L ] G' ++ x ~ T ++ G >> typ_var (avar_f x) <⦂ U << G2
| sa_fun : forall L G1 S1 U1 S2 U2 G2,
    [ L ] G2 >> S2 <⦂ S1 << G1 ->
    [ L ] G1 >> U1 <⦂ U2 << G2 ->
    [ L ] G1 >> typ_fun S1 U1 <⦂ typ_fun S2 U2 << G2
| sa_all : forall L x G1 S1 U1 S2 U2 G2,
    x `notin` fv G1 `union` fv S1 `union` fv S2
      `union` fv U1 `union` fv U2 `union` fv G2 `union` L ->
    [ L ] G2 >> S2 <⦂ S1 << G1 ->
    [ L `union` singleton x `union` fv S2 ]
      x ~ S1 ++ G1 >> open x U1 <⦂ open x U2 << x ~ S2 ++ G2 ->
    [ L ] G1 >> typ_all S1 U1 <⦂ typ_all S2 U2 << G2
where "[ L ] G1 >> T '<⦂' U << G2" := (stareat L G1 T U G2)%type.
Hint Constructors stareat.

(** Equivalence between strong kernel and stare-at subtyping *)
Section Equivalence.

  (** *** soundness of stare-at subtyping w.r.t. strong kernel F#<sub>&lt;:</sub># *)
  Theorem stareat_to_sk_subty : forall L' G1 S U G2,
    [ L' ] G1 >> S <⦂ U << G2 ->
    forall L,
      fv G1 `union` fv G2 `union` fv S `union` fv U `union` L [<=] L' ->
      [ L ] G1 ⊢k S <⦂ U ⊣ G2.
  Proof.
    induction on stareat; try solve [eroutine at 2]; intros.
    - econstructor; eauto.
      autorewrite with meta_ext in *.
      destruct_conjs.
      eapply sksub_weaken_l.
      eapply sksub_weaken_l.
      apply IHstareat.
      all:eauto.
      simpl in *. fsetdec.
    - constructor; eauto.
      + apply IHstareat1.
        simpl in *. fsetdec.
      + apply IHstareat2.
        simpl in *. fsetdec.
    - econstructor.
      + instantiate (1 := x).
        fsetdec.
      + apply IHstareat1.
        clear H. simpl in *. fsetdec.
      + apply IHstareat2.
        autorewrite with meta_ext in *.
        destruct_conjs.
        repeat split; set solve.
        * pose proof (fv_open_typ U1 x 0).
          simpl in *. fsetdec.
        * pose proof (fv_open_typ U2 x 0).
          simpl in *. fsetdec.
  Qed.

  Local Ltac wf_env :=
    lazymatch goal with
    | H : wf_env (_ ++ _) |- _ => apply wf_deapp in H; invert H; subst
    end.
  
  Ltac destruct_env_by x G :=
    let H := fresh "H" in
    assert (H : x `in` dom G) by set solve;
    apply in_to_binds in H; destruct_conjs;
    match goal with
    | H' : binds x _ G |- _ =>
      apply binds_app in H'; destruct_conjs;
      subst G
    end.

  Lemma ope_list_fv_env_subset : forall (G1 G2 : env),
      ope_list G1 G2 ->
      fv G1 [<=] fv G2.
  Proof.
    induction on @ope_list; set solve.
    all:destruct_conjs; simpl in *; fsetdec.
  Qed.

  Local Hint Constructors ope_list.
  
  Theorem stareat_strengthening : forall L G1 S U G2,
      [ L ] G1 >> S <⦂ U << G2 ->
      forall G1' G2',
        ope_list G1' G1 ->
        wf_env G1 -> wf_env G1' ->
        fv S [<=] dom G1' -> lc S ->
        ope_list G2' G2 ->
        wf_env G2 -> wf_env G2' ->
        fv U [<=] dom G2' -> lc U ->
        [ L ] G1' >> S <⦂ U << G2'.
  Proof.
    induction on stareat; intros; eauto.
    - destruct_env_by x G1'.
      constructor.
      pose proof (wf_uniq H0).
      pose proof (ope_list_witness_uniq H H13).
      destruct_conjs. subst.
      wf_env. do 2 apply wf_deapp in H0. progressive_inversions.
      eapply IHstareat; eauto.
    - progressive_inversions; simpl in *.
      auto 6.
    - pose proof (ope_list_dom H0).
      pose proof (ope_list_dom H5).
      pose proof (ope_list_fv_env_subset H0).
      pose proof (ope_list_fv_env_subset H5).
      pose proof (fv_open_typ U1 x 0).
      pose proof (fv_open_typ U2 x 0).
      
      progressive_inversions.
      econstructor.
      + instantiate (1 := x).
        fsetdec.
      + simpl in *. auto 6.
      + apply IHstareat2; simpl in *;
          try apply open_lc_typ;
          auto.
        3,6:clear H; fsetdec.
        all:constructor; simpl in *; auto; fsetdec.
  Qed.

  Hint Resolve ope_list_refl ope_list_trans ope_list_append2.
  
  (** *** completeness of stare-at subtyping w.r.t. strong kernel F#<sub>&lt;:</sub># *)
  Theorem sk_subty_to_stareat : forall L G1 S U G2,
      [ L ] G1 ⊢k S <⦂ U ⊣ G2 ->
      wf_env G1 -> wf_env G2 ->
      fv S [<=] dom G1 -> lc S ->
      fv U [<=] dom G2 -> lc U ->
      [ L ] G1 >> S <⦂ U << G2.
  Proof.
    induction on sk_subty; try solve [routine]; intros.
    - apply binds_witness in H.
      destruct_conjs. subst.
      pose proof H0. wf_env.
      econstructor.
      rec_pose IHsk_subty Hrec; auto.
      + set solve.
      + apply stareat_strengthening with (G1':=H7) (G2':= G2) in Hrec;
          auto.
        eauto.
    - econstructor.
      + instantiate (1 := x).
        trivial.
      + progressive_inversions.
        simpl in *.
        apply IHsk_subty1; auto.
      + pose proof (fv_open_typ U1 x 0).
        pose proof (fv_open_typ U2 x 0).
        progressive_inversions; simpl in *.
        apply IHsk_subty2;
          try apply open_lc_typ;
          auto.
        3-4:clear H; fsetdec.
        1-2:constructor; auto.
  Qed.        

  Theorem sk_subty_equiv_stareat : forall L G1 S U G2,
      wf_env G1 -> wf_env G2 ->
      fv S [<=] dom G1 -> lc S ->
      fv U [<=] dom G2 -> lc U ->
      [ fv G1 `union` fv G2 `union` fv S `union` fv U `union` L ] G1 ⊢k S <⦂ U ⊣ G2 <->
      [ fv G1 `union` fv G2 `union` fv S `union` fv U `union` L ] G1 >> S <⦂ U << G2.
  Proof.
    split; intros.
    - auto using sk_subty_to_stareat.
    - eapply stareat_to_sk_subty; eauto.
      fsetdec.
  Qed.
  
End Equivalence.


(** ** Termination of Stare-at Subtyping *)
Section Termination.

  Definition measure G T :=
    env_measure G + typ_struct_measure T.
  Arguments measure G T/.
  
  Inductive stareat_termination : forall L G1 S U G2, [ L ] G1 >> S <⦂ U << G2 -> Prop :=
  | st_top : forall L G1 T G2,
      stareat_termination (sa_top L G1 T G2)
  | st_tvrefl : forall L G1 x G2,
      stareat_termination (sa_tvrefl L G1 x G2)
  | st_tvar : forall L G G' x T U G2
                (Rec : [ L ] G >> T <⦂ U << G2),
                measure (G' ++ x ~ T ++ G) (typ_var (avar_f x)) +
                measure G2 U >
                measure G T + measure G2 U ->
                stareat_termination (sa_tvar G' x Rec)
  | st_fun : forall L G1 S1 U1 S2 U2 G2
               (Rec1 : [ L ] G2 >> S2 <⦂ S1 << G1)
               (Rec2 : [ L ] G1 >> U1 <⦂ U2 << G2),
      measure G1 (typ_fun S1 U1) + measure G2 (typ_fun S2 U2) >
      measure G1 S1 + measure G2 S2 ->
      measure G1 (typ_fun S1 U1) + measure G2 (typ_fun S2 U2) >
      measure G1 U1 + measure G2 U2 ->
      stareat_termination (sa_fun Rec1 Rec2)
  | st_all : forall L x G1 S1 U1 S2 U2 G2
               (NI : x `notin` fv G1 `union` fv S1 `union` fv S2
                       `union` fv U1 `union` fv U2 `union` fv G2 `union` L)
               (Rec1 : [ L ] G2 >> S2 <⦂ S1 << G1)
               (Rec2 : [ L `union` singleton x `union` fv S2 ]
                         x ~ S1 ++ G1 >> open x U1 <⦂ open x U2 << x ~ S2 ++ G2),
      measure G1 (typ_all S1 U1) + measure G2 (typ_all S2 U2) >
      measure G1 S1 + measure G2 S2 ->
      measure G1 (typ_all S1 U1) + measure G2 (typ_all S2 U2) >
      measure (x ~ S1 ++ G1) (open x U1) + measure (x ~ S2 ++ G2) (open x U2) ->
      stareat_termination (sa_all U1 U2 NI Rec1 Rec2).
  Hint Constructors stareat_termination.
  
  Fixpoint stareat_terminates L G1 S U G2
           (D : [ L ] G1 >> S <⦂ U << G2) {struct D} :
    stareat_termination D.
  Proof.
    destruct D; constructor; auto.
    all:simpl in *; autorewrite with measures in *; lia.
  Qed.

End Termination.
