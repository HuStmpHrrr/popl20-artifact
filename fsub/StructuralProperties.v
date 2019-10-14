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
Require Import Misc.
Require Import Program.
Require Import Arith.Wf_nat.

(** * Structural Properties of Full D#<sub>&lt;:</sub>#
    
    This file contains several structural properties, which are quite standard to prove.
    These structural properties include:
    - weakening,
    - transitivity,
    - narrowing, and
    - substitution.
 *)

Section StructuralProperties.
  
  Lemma weaken_subty_gen G S U: forall G1 G2,
      G1 ++ G2 ⊢F S <⦂ U -> G1 ++ G ++ G2 ⊢F S <⦂ U.
  Proof.
    - intros. generalize dependent G.
      dependent induction H; intros; trivial.
      + apply binds_weaken with (F := G) in H.
        econstructor; eauto.
      + constructor; eroutine.
      + eapply st_all; eroutine.
        reassoc 4 with 2. apply H1; routine.
  Qed.

  Definition weaken_subty G S U: forall G',
      G ⊢F S <⦂ U -> G' ++ G ⊢F S <⦂ U.
  Proof.
    intros. reassoc 2 with 0.
    apply weaken_subty_gen; simpl; trivial.
  Qed.

  Section Reflexivity.
    
    Hint Extern 1 (_ <= _) => autorewrite with measures; simpl; lia.

    Program Fixpoint subty_refl T {measure (typ_struct_measure T)} : forall G,
      G ⊢F T <⦂ T := _.
    Next Obligation.
      destruct T; routine.
      pose proof (typ_struct_measure_ge_1 T1).
      pose proof (typ_struct_measure_ge_1 T2).
      econstructor; routine.
    Qed.

  End Reflexivity.
  
  (** transitivity in F#<sub>&lt;:</sub># is a bit easier to setup as the All case is the only complicated case.
   *)
  Section Transitivity.

    Inductive narrow T : nat -> env -> env -> Prop :=
    | n_first : forall G x S, G ⊢F S <⦂ T -> narrow T 0 (x ~ S ++ G) (x ~ T ++ G)
    | n_cons : forall G1 G2 n x T', narrow T n G1 G2 -> narrow T (S n) (x ~ T' ++ G1) (x ~ T' ++ G2).
    Local Hint Constructors narrow.
    
    Definition trans_on T : Prop :=
      forall G S U, G ⊢F S <⦂ T -> G ⊢F T <⦂ U -> G ⊢F S <⦂ U.
    
    Definition narrow_on T : Prop :=
      forall G S U, G ⊢F S <⦂ U -> forall n G', narrow T n G' G -> G' ⊢F S <⦂ U.
    Arguments trans_on T/.
    Arguments narrow_on T/.
    
    Hint Extern 1 (_ < _) => autorewrite with measures; simpl; lia.

    Lemma trans_hyp : forall T,
        (forall T', typ_struct_measure T' < typ_struct_measure T -> trans_on T' /\ narrow_on T') ->
        trans_on T.
    Proof.
      simpl. intros. induction H0; dependent induction H1; try solve [eroutine].
      - clear IHsubty0 IHsubty1 IHsubty2 IHsubty3.
        constructor.
        + apply (H T1); routine.
        + apply (H T2); routine.
      - clear IHsubty IHsubty0 H3 H5.
        econstructor.
        + apply (H T1); routine.
        + cofinite.
          rec_pose (H2 x) Hsub1; auto.
          rec_pose (H4 x) Hsub2; auto.
          apply (H (open x T2)); auto.
          rec_pose (H T1) Hrec; auto.
          destruct_conjs. eapply H5; auto.
    Qed.

    Inductive binds_n : var -> typ -> nat -> env -> Prop :=
    | bn_found : forall x T G, binds_n x T 0 ((x, T) :: G)
    | bn_cons :  forall x T n G y U, binds_n x T n G -> binds_n x T (S n) ((y, U) :: G).
    Local Hint Constructors binds_n.

    Lemma binds_n_to_binds : forall x T n G,
        binds_n x T n G -> binds x T G.
    Proof. induction on binds_n; routine. Qed.

    Lemma binds_to_binds_n : forall x T G,
        binds x T G -> exists n, binds_n x T n G.
    Proof.
      induction G; eroutine.
      specialize (IHG H). tidy_up.
      exists (S IHG). constructor. trivial.
    Qed.

    Lemma binds_equiv_binds_n : forall x T G,
        binds x T G <-> exists n, binds_n x T n G.
    Proof.
      split.
      - apply binds_to_binds_n.
      - routine. eauto using binds_n_to_binds.
    Qed.

    Lemma narrow_binds_n : forall T n G G',
        narrow T n G' G ->
        forall y T' m,
          binds_n y T' m G ->
          (m = n /\ T = T' /\ exists T'', binds_n y T'' m G' /\ (G' ⊢F T'' <⦂ T)) \/
          (m <> n /\ binds_n y T' m G').
    Proof.
      induction on narrow; routine.
      - invert H1; routine.
        left. repeat (split || eexists); eroutine.
        apply weaken_subty with (G' := x ~ S).
        trivial.
      - invert H0; routine.
        specialize (IHnarrow _ _ _ H6); routine.
        left. repeat (split || eexists); eroutine.
        apply weaken_subty with (G' := x ~ T').
        trivial.
    Qed.
    
    Lemma narrow_hyp : forall T,
        (forall T', typ_struct_measure T' = typ_struct_measure T -> trans_on T') ->
        narrow_on T.
    Proof.
      simpl. induction 2; eroutine.
      - specialize (IHsubty _ _ H2).
        rewrite binds_equiv_binds_n in H0.
        tidy_up.
        pose proof (narrow_binds_n H2 H3).
        tidy_up.
        + apply binds_n_to_binds in H7. econstructor; eauto.
        + apply binds_n_to_binds in H5. econstructor; eauto.
      - econstructor. eauto.
        cofinite.
        specialize (H1 x ltac:(auto)).
        rec_pose (H2 x ltac:(auto)) Hrec; eauto.
        econstructor. eauto.
    Qed.
    
    Program Fixpoint trans_and_narrow T {measure (typ_struct_measure T)} :
      trans_on T /\ narrow_on T := _.
    Next Obligation.
      split.
      - apply trans_hyp. auto.
      - apply narrow_hyp.
        intros. apply trans_hyp.
        intros. apply trans_and_narrow.
        auto.
    Qed.

    Theorem subty_trans : forall G S T U,
        G ⊢F S <⦂ T -> G ⊢F T <⦂ U -> G ⊢F S <⦂ U.
    Proof.
      intros. apply (trans_and_narrow T); auto.
    Qed.

  End Transitivity.
    
  Hint Resolve subst_open_comm_typ.
    
  Definition subst_env (z u: var) (G : env) : env := map (substi z u) G.

  Global Instance SubstiEnv : CanSubst env := { substi := subst_env }.

  Lemma free_all : forall x y T (G : env),
      y `notin` fv G ->
      binds x T G ->
      y `notin` fv T.
  Proof. induction on env; routine. Qed.

  Local Ltac fold_env :=
    lazymatch goal with
      |- context[?v ~ substi ?x ?y ?T ++ substi ?x ?y ?G] =>
      change (v ~ substi x y T ++ substi x y G)
    with (substi x y (v ~ T ++ G))
    end.

  Ltac apply_ind H := solve [eapply H; routine].

  Ltac fold_subst_fvar :=
    repeat match goal with
           | |- context[if ?x == ?y then ?z else ?x] =>
             change (if x == y then z else x) with (subst_fvar y z x)
           end.

  Ltac solve_by_weaken H :=
    cofinite; fold_substi;
    open_substi_transform;
    reassoc 3 with 2; fold_env;
    eapply H; routine;
    simpl_env;
    try apply weaken_subty; eauto.
  
  Lemma subty_subst_gen : forall x X S U G1 G2 y,
      G2 ++ x ~ X ++ G1 ⊢F S <⦂ U ->
      uniq (G2 ++ x ~ X ++ G1) ->
      x `notin` fv G1 ->
      forall Y,
        binds y Y (substi x y G2 ++ G1) ->
        substi x y G2 ++ G1 ⊢F Y <⦂ substi x y X ->
        substi x y G2 ++ G1 ⊢F substi x y S <⦂ substi x y U.
  Proof.
    intros. gen y Y. dependent induction H; intros; trivial.
    - simpl. auto.
    - simpl. destruct_eq.
      + econstructor; eauto.
        destruct_binds_hyp_uniq H; simpl dom in *; try solve_notin.
        eapply subty_trans. eassumption.
        apply_ind IHsubty.
      + destruct_binds_hyp_uniq H; simpl dom in *; try solve_notin.
        * econstructor.
          -- apply binds_app_2.
             apply binds_map_2.
             eassumption.
          -- apply_ind IHsubty.
        * econstructor; eauto.
          rewrite <- (@subst_fresh_typ x y T).
          -- apply_ind IHsubty.
          -- eapply free_all; eassumption.
    - simpl.
      apply st_fun; [apply_ind IHsubty1 | apply_ind IHsubty2].
    - simpl. eapply st_all.
      + apply_ind IHsubty.
      + solve_by_weaken H1.
  Qed.

  Lemma subty_subst : forall x X S U G y,
      x ~ X ++ G ⊢F S <⦂ U ->
      uniq (x ~ X ++ G) ->
      x `notin` fv G ->
      forall Y,
        binds y Y G ->
        G ⊢F Y <⦂ substi x y X ->
      G ⊢F substi x y S <⦂ substi x y U.
  Proof.
    intros. change G with (substi x y nil ++ G).
    eapply subty_subst_gen; routine.
  Qed.

  Ltac prelude :=
    intros;
    try erewrite subst_intro_typ.
  
  Ltac fin :=
    try eapply subty_subst;
    routine;
    try (simpl; fold_substi; fold_open_rec;
         eexrewrite subst_fresh_typ);
    routine.

  Lemma renaming_subty : forall G z T S U (x : var),
      uniq G ->
      z `notin` fv G `union` fv T `union` fv U `union` fv S ->
      z ~ T ++ G ⊢F open z S <⦂ open z U ->
      forall X,
        binds x X G ->
        G ⊢F X <⦂ T ->
        G ⊢F open x S <⦂ open x U.
  Proof using.
    prelude.
    erewrite subst_intro_typ with (t := U).
    all:fin.
  Qed.

  Hint Resolve subty_refl.
  
  Lemma open_subst_subty : forall x S G U1 U2 y,
      uniq G ->
      x `notin` fv G `union` fv S `union` fv U1 `union` fv U2 ->
      y `notin` fv G `union` fv S `union` fv U1 `union` fv U2 `union` singleton x ->
      x ~ S ++ G ⊢F open x U1 <⦂ open x U2 ->
      y ~ S ++ G ⊢F open y U1 <⦂ open y U2.
  Proof.
    intros.
    apply renaming_subty with (z := x) (T := S) (X := S); routine.
    simpl_env.
    apply weaken_subty_gen. trivial.
  Qed.

End StructuralProperties.

Hint Resolve subty_trans subty_refl.
