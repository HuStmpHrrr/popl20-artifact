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

(** * Structural Properties of Full D#<sub>&lt;:</sub>#
    
    This file contains several structural properties, which are quite standard to prove.
    These structural properties include:
    - weakening,
    - narrowing, and
    - substitution.
 *)

Section StructuralProperties.
  
  Lemma weaken_typing_gen G t T: forall G1 G2,
    G1 ++ G2 ⊢ t ⦂ T -> G1 ++ G ++ G2 ⊢ t ⦂ T
  with weaken_subty_gen G S U: forall G1 G2,
      G1 ++ G2 ⊢ S <⦂ U -> G1 ++ G ++ G2 ⊢ S <⦂ U.
  Proof.
    - intros. generalize dependent G.
      dependent induction H; intros.
      + constructor. routine.
      + constructor.
      + econstructor. cofinite.
        reassoc 4 with 2.
        apply H0; routine.
      + econstructor; eroutine.
      + econstructor; eroutine.
        reassoc 4 with 2.
        apply H1; routine.
      + eapply ty_sub.
        * apply IHtyping; trivial.
        * apply weaken_subty_gen; trivial.

    - intros. generalize dependent G.
      dependent induction H; intros; trivial.
      + eapply st_trans; [ apply IHsubty1 | apply IHsubty2]; trivial.
      + constructor; routine.
      + eapply st_all; eroutine.
        reassoc 4 with 2. apply H1; routine.
      + eapply st_sel1.
        eapply weaken_typing_gen; eroutine.
      + eapply st_sel2.
        eapply weaken_typing_gen; eroutine.
  Qed.

  Definition weaken_typing G t T: forall G',
      G ⊢ t ⦂ T -> G' ++ G ⊢ t ⦂ T.
  Proof.
    intros. reassoc 2 with 0.
    apply weaken_typing_gen; simpl; trivial.
  Qed.

  Definition weaken_subty G S U: forall G',
      G ⊢ S <⦂ U -> G' ++ G ⊢ S <⦂ U.
  Proof.
    intros. reassoc 2 with 0.
    apply weaken_subty_gen; simpl; trivial.
  Qed.
  
  Hint Resolve subst_open_comm_trm.
  Hint Resolve subst_open_comm_typ.
  
  Local Ltac to_substi :=
    lazymatch goal with
      |- context[trm_var (avar_f (if ?x == ?y then ?z else ?x))] =>
      change (trm_var (avar_f (if x == y then z else x)))
    with (substi y z (trm_var (avar_f x)))
    end.
  
  
  Definition subst_env (z u: var) (G : env) : env := map (substi z u) G.

  Global Instance SubstiEnv : CanSubst env := { substi := subst_env }.

  Lemma free_all : forall x y T (G : env),
      y `notin` fv G ->
      binds x T G ->
      y `notin` fv T.
  Proof. induction on env; routine. Qed.

  Lemma subst_trm_var : forall G1 G2 x0 y x T X,
      binds x0 T (G2 ++ x ~ X ++ G1) ->
      uniq (G2 ++ x ~ X ++ G1) ->
      x `notin` fv G1 ->
      substi x y G2 ++ G1 ⊢ trm_var (avar_f y) ⦂ substi x y X ->
      substi x y G2 ++ G1 ⊢ trm_var (avar_f $ subst_fvar x y x0) ⦂ substi x y T.
  Proof.
    intros. destruct_binds_hyp_uniq H; tidy_up.
    - constructor. unfold subst_env.
      apply binds_app_2.
      apply binds_map_2. trivial.
    - trivial.
    - exrewrite subst_fresh_typ.
      + auto.
      + eapply free_all; try eassumption.
        simpl. solve_notin.
  Qed.

  Local Ltac fold_env :=
    lazymatch goal with
      |- context[?v ~ substi ?x ?y ?T ++ substi ?x ?y ?G] =>
      change (v ~ substi x y T ++ substi x y G)
    with (substi x y (v ~ T ++ G))
    end.

  Ltac solve_by_weaken H :=
    cofinite; fold_substi;
    open_substi_transform;
    reassoc 3 with 2; fold_env;
    eapply H; routine;
    simpl_env;
    apply weaken_typing; trivial.

  Ltac apply_ind H := solve [eapply H; routine].

  Ltac fold_subst_fvar :=
    repeat match goal with
           | |- context[if ?x == ?y then ?z else ?x] =>
             change (if x == y then z else x) with (subst_fvar y z x)
           end.
  
  Lemma typing_subst_gen : forall x X t T G1 G2 y,
      G2 ++ x ~ X ++ G1 ⊢ t ⦂ T ->
      uniq (G2 ++ x ~ X ++ G1) ->
      x `notin` fv G1 ->
      substi x y G2 ++ G1 ⊢ trm_var (avar_f y) ⦂ substi x y X ->
      substi x y G2 ++ G1 ⊢ substi x y t ⦂ substi x y T
  with subty_subst_gen : forall x X S U G1 G2 y,
      G2 ++ x ~ X ++ G1 ⊢ S <⦂ U ->
      uniq (G2 ++ x ~ X ++ G1) ->
      x `notin` fv G1 ->
      substi x y G2 ++ G1 ⊢ trm_var (avar_f y) ⦂ substi x y X ->
      substi x y G2 ++ G1 ⊢ substi x y S <⦂ substi x y U.
  Proof.
    - clear typing_subst_gen.
      intros. gen y. dependent induction H; intros.
      + simpl. eapply subst_trm_var. all:try eassumption.
      + constructor.
      + simpl. econstructor. solve_by_weaken H0.
      + simpl. fold_substi. fold_open_rec. fold_subst_fvar.
        rewrite subst_open_comm_typ. econstructor.
        * apply_ind IHtyping1.
        * apply_ind IHtyping2.
      + simpl; econstructor.
        * apply_ind IHtyping.
        * solve_by_weaken H1.
      + eapply ty_sub.
        * apply_ind IHtyping.
        * apply_ind subty_subst_gen.

    - clear subty_subst_gen.
      intros. gen y. dependent induction H; intros; trivial.
      + eapply st_trans.
        * apply_ind IHsubty1.
        * apply_ind IHsubty2.
      + simpl.
        apply st_bnd; [apply_ind IHsubty1 | apply_ind IHsubty2].
      + simpl. eapply st_all.
        * apply_ind IHsubty.
        * solve_by_weaken H1.
      + eapply st_sel1.
        eapply typing_subst_gen in H; routine.
      + eapply st_sel2.
        eapply typing_subst_gen in H; routine.
  Qed.

  Lemma typing_subst : forall x X t T G y,
      x ~ X ++ G ⊢ t ⦂ T ->
      uniq (x ~ X ++ G) ->
      x `notin` fv G ->
      G ⊢ trm_var (avar_f y) ⦂ substi x y X ->
      G ⊢ substi x y t ⦂ substi x y T.
  Proof.
    intros. change G with (substi x y nil ++ G).
    eapply typing_subst_gen; routine.
  Qed.

  Lemma subty_subst : forall x X S U G y,
      x ~ X ++ G ⊢ S <⦂ U ->
      uniq (x ~ X ++ G) ->
      x `notin` fv G ->
      G ⊢ trm_var (avar_f y) ⦂ substi x y X ->
      G ⊢ substi x y S <⦂ substi x y U.
  Proof.
    intros. change G with (substi x y nil ++ G).
    eapply subty_subst_gen; routine.
  Qed.

  Ltac prelude :=
    intros;
    try erewrite subst_intro_typ;
    try erewrite subst_intro_trm.
  
  Ltac fin :=
    try (eapply typing_subst || eapply subty_subst);
    routine;
    try (simpl; fold_substi; fold_open_rec;
         eexrewrite subst_fresh_typ);
    routine.
  
  Lemma renaming_trm : forall G z t T U (x : var),
      uniq G ->
      z `notin` fv G `union` fv T `union` fv U `union` fv t ->
      z ~ U ++ G ⊢ open z t ⦂ open z T ->
      G ⊢ trm_var (avar_f x) ⦂ U ->
      G ⊢ open x t ⦂ open x T.
  Proof using. prelude; fin. Qed.

  Lemma renaming_subty : forall G z T S U (x : var),
      uniq G ->
      z `notin` fv G `union` fv T `union` fv U `union` fv S ->
      z ~ T ++ G ⊢ open z S <⦂ open z U ->
      G ⊢ trm_var (avar_f x) ⦂ T ->
      G ⊢ open x S <⦂ open x U.
  Proof using.
    prelude.
    erewrite subst_intro_typ with (t := U).
    all:fin.
  Qed.
  
  Lemma renaming_fresh : forall L G T u U (x : var),
      uniq G ->
      (forall x, x `notin` L -> x ~ T ++ G ⊢ open x u ⦂ U) ->
      G ⊢ trm_var (avar_f x) ⦂ T ->
      G ⊢ open x u ⦂ U.
  Proof using. intros;
                 let z := fresh in
                 pick_fresh z; prelude;
                   try instantiate (1 := z);
                   try eexrewrite <- subst_fresh_typ;
                   fin.
  Qed.
  
  Lemma open_subst_typing : forall x S G t U y,
      uniq G ->
      x `notin` fv G `union` fv S `union` fv U `union` fv t ->
      y `notin` fv G `union` fv S `union` fv U `union` fv t `union` singleton x ->
      x ~ S ++ G ⊢ open x t ⦂ open x U ->
      y ~ S ++ G ⊢ open y t ⦂ open y U.
  Proof.
    intros.
    apply renaming_trm with (z := x) (U := S); routine.
    simpl_env.
    apply weaken_typing_gen. trivial.
  Qed.

  Lemma open_subst_subty : forall x S G U1 U2 y,
      uniq G ->
      x `notin` fv G `union` fv S `union` fv U1 `union` fv U2 ->
      y `notin` fv G `union` fv S `union` fv U1 `union` fv U2 `union` singleton x ->
      x ~ S ++ G ⊢ open x U1 <⦂ open x U2 ->
      y ~ S ++ G ⊢ open y U1 <⦂ open y U2.
  Proof.
    intros.
    apply renaming_subty with (z := x) (T := S); routine.
    simpl_env.
    apply weaken_subty_gen. trivial.
  Qed.

  Reserved Notation "G1 ⪯ G2" (at level 70).

  Inductive subenv: env -> env -> Prop :=
  | subenv_empty : nil ⪯ nil
  | subenv_grow: forall G G' x T T',
      G ⪯ G' ->
      uniq ((x, T) :: G) ->
      uniq ((x, T') :: G') ->
      G ⊢ T <⦂ T' ->
      (x, T) :: G ⪯ (x, T') :: G'
  where "G1 ⪯ G2" := (subenv G1 G2).
  Hint Constructors subenv.

  Lemma subenv_refl : forall G, uniq G -> G ⪯ G.
  Proof. induction G; eroutine. Qed.
  Local Hint Resolve subenv_refl.

  Lemma subenv_push : forall G1 G2 x T,
      G1 ⪯ G2 ->
      uniq ((x, T) :: G1) ->
      uniq ((x, T) :: G2) ->
      (x, T) :: G1 ⪯ (x, T) :: G2.
  Proof. induction G1; eroutine. Qed.
  Local Hint Resolve subenv_push.

  Local Hint Extern 1 =>
  match goal with
  | [ H : uniq _ |- _ ] => inversion H
  end.

  Local Hint Extern 1 =>
  match goal with
  | [ H : _ ⪯ _ |- _ ] => inversion H
  end.
  
  Lemma subenv_last: forall G x S U,
      G ⊢ S <⦂ U ->
      uniq ((x, S) :: G) ->
      (x, S) :: G ⪯ (x, U) :: G.
  Proof. routine. Qed.
  Hint Resolve subenv_last.

  Lemma subenv_implies_uniq : forall G1 G2,
      G1 ⪯ G2 -> uniq G1 /\ uniq G2.
  Proof. routine. Qed.

  Local Hint Extern 1 =>
  match goal with
  | [ |- _ ⊢ _ <⦂ _ ] => idtac
  | [ |- _ ⊢ _ ⦂ _ ] => idtac
  end; reassoc 2 with 0.
  
  Local Hint Extern 1 => eapply weaken_typing.
  Local Hint Extern 1 => eapply weaken_subty.
  
  Lemma narrow_var :
    forall G G' x T,
      G' ⪯ G ->
      binds x T G ->
      G' ⊢ trm_var (avar_f x) ⦂ T.
  Proof.
    induction on subenv; intros.
    - routine.
    - change ((x , T') :: G') with (x ~ T' ++ G') in *.
      eapply binds_app_uniq_iff in H0.
      apply H0 in H5. destruct H5; tidy_up.
      + eapply ty_sub; simpl_env;
          [ | eapply weaken_subty; eassumption].
        constructor; auto.
      + routine.
  Qed.
  
  Local Notation narrowing ctor :=
    (forall G t T, ctor G t T -> forall G',
          G' ⪯ G ->
          ctor G' t T).

  Local Ltac uniq_env :=
    match goal with
    | [ H : _ ⪯ _ |- _ ] =>
      let H0 := fresh "H" in
      pose proof (subenv_implies_uniq H) as H0;
      destruct H0
    end.

  Local Ltac solve_by_cofinite H :=
    cofinite; apply H;
    [ solve_notin |
      constructor; trivial;
      constructor; trivial; solve_notin].
  
  Lemma narrow_typing_gen : narrowing typing
  with narrow_subty_gen : narrowing subty.
  Proof.
    - clear narrow_typing_gen.
      induction on typing; routine; uniq_env.
      + eapply narrow_var; eassumption.
      + econstructor. solve_by_cofinite H0.
      + econstructor; routine.
      + econstructor. routine.
        solve_by_cofinite H0.
      + eapply ty_sub. routine.
        eapply narrow_subty_gen; eassumption.

    - clear narrow_subty_gen.
      induction on subty; routine; uniq_env.
      + eapply st_trans;
          [apply IHsubty1 | apply IHsubty2]; trivial.
      + eapply st_all;
          [routine | solve_by_cofinite H0].
      + eapply st_sel1.
        eapply narrow_typing_gen; eassumption.
      + eapply st_sel2.
        eapply narrow_typing_gen; eassumption.
  Qed.

  Lemma narrow_typing : forall x S1 S2 G t T,
      x ~ S2 ++ G ⊢ t ⦂ T ->
      x `notin` dom G ->
      uniq G ->
      G ⊢ S1 <⦂ S2 ->
      x ~ S1 ++ G ⊢ t ⦂ T.
  Proof.
    intros. eapply narrow_typing_gen.
    apply H.
    constructor; trivial.
    auto.
    all:solve_uniq.
  Qed.
  
  Lemma narrow_subty : forall x S1 S2 G U1 U2,
      x ~ S2 ++ G ⊢ U1 <⦂ U2 ->
      x `notin` dom G ->
      uniq G ->
      G ⊢ S1 <⦂ S2 ->
      x ~ S1 ++ G ⊢ U1 <⦂ U2.
  Proof.
    intros. eapply narrow_subty_gen.
    apply H.
    constructor; trivial.
    auto.
    all:solve_uniq.
  Qed.
  
End StructuralProperties.

Hint Resolve subenv_refl subenv_push subenv_last.
