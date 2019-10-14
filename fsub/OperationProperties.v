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

(** * Properties of Operations

    This file contains properties of characteristics and operations. They are very
    much technical details so it usually should not concern readers. 
 *)

Section LcOpenClosingProperties.

  Local Notation lc_relax T :=
    (forall (v : T) n m, lc_at n v -> n <= m -> lc_at m v).

  Local Hint Extern 1 => lia.
  
  Lemma lc_relax_avar : lc_relax avar.
  Proof using. induction 1; routine. Qed.
  Hint Resolve lc_relax_avar.

  Lemma lc_relax_typ : lc_relax typ.
  Proof using.
    intros. gen m.
    induction H; eroutine.
  Qed.
  Hint Resolve lc_relax_typ.

  Local Notation open_lc T :=
    (forall (v : T) n x, lc_at (S n) v -> lc_at n (open_rec n x v)).
  
  Lemma open_lc_avar : open_lc avar.
  Proof using.
    intros. invert H.
    - destruct_eq; routine.
    - routine.
  Qed.
  Hint Resolve open_lc_avar.

  Lemma open_lc_typ : open_lc typ.
  Proof using.
    intros. simpl in H.
    dependent induction H; routine.
  Qed.
  Hint Resolve open_lc_typ.

  Local Notation open_lc_le T :=
    (forall (v : T) n m x, lc_at n v -> m >= n -> open_rec m x v = v).

  Lemma open_lc_le_avar : open_lc_le avar.
  Proof. destr on avar; routine. Qed.

  Lemma open_lc_le_typ : open_lc_le typ.
  Proof.
    induction on typ; routine.
    eapply open_lc_le_avar; eassumption.
    all:ctx_app; try eassumption; lia.
  Qed.
      
  Local Notation open_lc_inv T :=
    (forall (v : T) n x, lc_at n (open_rec n x v) -> lc_at (S n) v).
  
  Lemma open_lc_inv_avar : open_lc_inv avar.
  Proof using.
    intros. simpl in H. invert H.
    - destruct v; routine.
    - destruct v; routine.
  Qed.
  Hint Resolve open_lc_inv_avar.

  Lemma open_lc_inv_typ : open_lc_inv typ.
  Proof using. induction on typ; eroutine. Qed.
  Hint Resolve open_lc_inv_typ.

  Local Notation open_left_inv T :=
    (forall (v : T) n x, lc_at n v -> open_rec n x (close_rec n x v) = v).

  Lemma open_left_inv_avar : open_left_inv avar.
  Proof using. induction 1; routine. Qed.
  Hint Resolve open_left_inv_avar.

  Lemma open_left_inv_typ : open_left_inv typ.
  Proof using. induction 1; routine. Qed.
  Hint Resolve open_left_inv_typ.

  Local Notation close_lc T :=
    (forall (v : T) n x, lc_at n v -> lc_at (S n) (close_rec n x v)).
  
  Lemma close_lc_avar : close_lc avar.
  Proof. induction on avar; routine. Qed.
  Hint Resolve close_lc_avar.
  
  Lemma close_lc_typ : close_lc typ.
  Proof. induction on typ; routine. Qed.
  Hint Resolve close_lc_typ.

End LcOpenClosingProperties.

Section OpenFreshInj.
  
  Variable z : atom.

  Local Notation fresh_inj T :=
    (forall (x y : T) k,
        z `notin` fv x ->
        z `notin` fv y ->
        open_rec k z x = open_rec k z y ->
        x = y).
  
  Lemma open_fresh_inj_avar : fresh_inj avar.
  Proof using.
    intros. destruct x, y; routine.
  Qed.
  Local Hint Resolve open_fresh_inj_avar.

  Local Ltac boom :=
    eroutine by 
      (idtac; match goal with
              | [ H : _ = _ _ z ?t' |- _ ] =>
                destruct t'; inversion H
              end).
  
  Lemma open_fresh_inj_typ: fresh_inj typ.
  Proof using. induction on typ; boom. Qed.
  Hint Resolve open_fresh_inj_typ.
  
End OpenFreshInj.

Section SubstFresh.
  
  Variable x y : var.

  Local Notation subst_fresh T :=
    (forall t : T, x `notin` fv t -> substi x y t = t).

  Lemma subst_fresh_avar : subst_fresh avar.
  Proof using.
    intros. destruct t; routine.
  Qed.
  Local Hint Resolve subst_fresh_avar.

  Lemma subst_fresh_typ : subst_fresh typ.
  Proof using. induction on typ; routine. Qed.
  Hint Resolve subst_fresh_typ.
  
End SubstFresh.

Section SubstOpenComm.

  Variable x y : var.

  (** z[y/x] *)
  Definition subst_fvar (z : var) : var :=
    if z == x then y else z.

  Local Notation subst_open_comm T u :=
    (forall (t : T) (n : nat),
        substi x y (open_rec n u t) =
        open_rec n (subst_fvar u) $ substi x y t).

  Lemma subst_open_comm_avar : forall u,
      subst_open_comm avar u.
  Proof using.
    intros. destruct t; routine by (unfold subst_fvar).
  Qed.
  Hint Resolve subst_open_comm_avar.
  
  Lemma subst_open_comm_typ : forall u, subst_open_comm typ u.
  Proof using. induction on typ; routine. Qed.
  Hint Resolve subst_open_comm_typ.

End SubstOpenComm.
Arguments subst_fvar x y z/.
Hint Unfold subst_fvar.

Section SubstIntro.

  Local Notation subst_intro T :=
    (forall x u (t : T) (n : nat),
        x `notin` fv t ->
        open_rec n u t = substi x u $ open_rec n x t).
  
  Local Hint Extern 1 => exrewrite subst_fresh_typ.

  Local Ltac boom := routine by
        (exrewrite subst_open_comm_typ).
  
  Lemma subst_intro_typ : subst_intro typ.
  Proof using. boom. Qed.

End SubstIntro.

Section SubstFvarProps.
  Variable x y z : var.
  Variable T : Type.

  Context {SubstT : CanSubst T} {OpenT : CanOpen T}.

  Variable t : T.

  Lemma open_substi_rewrite :
    z `notin` singleton x `union` singleton y ->
    open z (substi x y t) =
    open (subst_fvar x y z) (substi x y t).
  Proof using. routine. Qed.

  Hypothesis subst_open_comm :
    substi x y (open z t) = open (subst_fvar x y z) (substi x y t).
  
  
  Lemma open_substi_rewrite2 :
    z `notin` singleton x `union` singleton y ->
    open z (substi x y t) =
    substi x y (open z t).
  Proof.
    intros. rewrite open_substi_rewrite by auto.
    rewrite <- subst_open_comm. trivial.
  Qed.

End SubstFvarProps.

Ltac open_substi_transform :=
  repeat match goal with
         | |- context[?f ?v (substi ?x ?y ?t)] =>
           lazymatch f with
           | context[open] => idtac
           end;
           lazymatch v with
           | context[subst_fvar] => fail
           | _ => idtac
           end;
           replace (f v (substi x y t)) with (substi x y (open v t))
             by (rewrite open_substi_rewrite; auto)
         end.

Section FvOpen.

  Local Notation fv_open T :=
    (forall (v : T) x n, fv (open_rec n x v) [<=] singleton x \u fv v).
  
  Lemma fv_open_avar : fv_open avar.
  Proof.
    induction on avar; intros; simpl.
    - progressive_destructions; set solve.
    - set solve.
  Qed.
  Hint Resolve fv_open_avar.

  Local Ltac union_pf :=
    apply AtomSetProperties.union_subset_3;
    etransitivity; try eassumption; set solve.

  Local Ltac fold_cls :=
    fold_open_rec; fold_fv.
  
  Lemma fv_open_typ : fv_open typ.
  Proof.
    induction on typ; intros; simpl; set solve.
    - fold_cls.
      specialize (IHtyp1 x n).
      specialize (IHtyp2 x n).
      union_pf.
    - fold_cls.
      specialize (IHtyp1 x n).
      specialize (IHtyp2 x (S n)).
      union_pf.
  Qed.

End FvOpen.

Section FvClose.

  Local Notation fv_close_self T :=
    (forall (v : T) x n, x `notin` fv (close_rec n x v)).

  Lemma fv_close_self_avar : fv_close_self avar.
  Proof. intros. destruct v; routine. Qed.

  Hint Resolve AtomSetProperties.not_in_union.
  
  Lemma fv_close_self_typ : fv_close_self typ.
  Proof.
    induction on typ; intros; auto.
    apply fv_close_self_avar.
  Qed.    

  Ltac pf_union := apply AtomSetProperties.not_in_union.

  Local Notation fv_close T :=
    (forall (v : T) x n, fv (close_rec n x v) [<=] fv v).

  Lemma fv_close_avar : fv_close avar.
  Proof.
    intros. destruct v; auto.
    destruct_eq; set solve.
  Qed.

  Ltac pf_union ::= apply AtomSetProperties.union_subset_3.
  
  Lemma fv_close_typ : fv_close typ.
  Proof.
    induction on typ; intros; auto.
    - apply fv_close_avar.
    - simpl.
      specialize (IHtyp1 x n).
      specialize (IHtyp2 x n).
      pf_union; set solve.
    - simpl.
      specialize (IHtyp1 x n).
      specialize (IHtyp2 x (S n)).
      pf_union; set solve.
  Qed.

  Local Notation fv_add_close T :=
    (forall (v : T) x (G : env) n, fv v [<=] add x (dom G) ->
                              fv (close_rec n x v) [<=] dom G).
  
  Lemma fv_add_close_avar : fv_add_close avar.
  Proof.
    intros. destruct v; simpl in *.
    - set solve.
    - destruct_eq. set solve.
      rewrite AtomSetProperties.add_union_singleton in H.
      apply AtomSetImpl.union_1 with (x := a) in H.
      destruct H.
      + apply AtomSetImpl.singleton_1 in H.
        congruence.
      + autounfold. simpl. intros.
        apply AtomSetImpl.singleton_1 in H0.
        subst. trivial.
      + apply AtomSetImpl.singleton_2. trivial.
  Qed.

  
  Lemma fv_add_close_typ : fv_add_close typ.
  Proof.
    induction on typ; intros; set solve.
    - apply fv_add_close_avar. trivial.
    - simpl in *.
      pf_union; [apply IHtyp1 | apply IHtyp2];
        set solve.
    - simpl in *.
      pf_union; [apply IHtyp1 | apply IHtyp2];
        set solve.
  Qed.
  
End FvClose.
