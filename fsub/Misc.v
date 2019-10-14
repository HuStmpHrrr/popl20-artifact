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

(** * Miscellaneous Definitions

    This file defines well-formedness of contexts, and some structural measures. The
 definitions resembles those in D<:, so we do not repeat here.
  *)

Inductive wf_env : env -> Prop :=
| wf_nil : wf_env nil
| wf_cons : forall {x T G}, x \notin fv T \u fv G ->
                       fv T [<=] dom G ->
                       wf_env G ->
                       lc T ->
                       wf_env (x ~ T ++ G).
Hint Constructors wf_env.

Lemma wf_decons : forall x T G, wf_env (x ~ T ++ G) -> x \notin fv T.
Proof. routine. Qed.

Lemma wf_deapp : forall G1 G2, wf_env (G1 ++ G2) -> wf_env G2.
Proof. induction on env; routine. Qed.

Lemma wf_uniq : forall G, wf_env G -> uniq G.
Proof. induction on env; routine. Qed.

Lemma wf_var_in : forall G1 G2 v,
    wf_env (G1 ++ G2) ->
    v `in` dom G2 ->
         v `notin` dom G1.
Proof.
  induction G1; intros.
  - routine.
  - tidy_up. repeat rewrite dom_app in *.
    destruct_notin.
    rewrite AtomSetProperties.add_union_singleton.
    intro Contra.
    apply AtomSetImpl.union_1 in Contra.
    destruct Contra.
    + apply AtomSetImpl.singleton_1 in H1. subst.
      intuition.
    + eapply IHG1; eassumption.
Qed.        

Lemma wf_fv_is_dom : forall G,
    wf_env G ->
    fv G [=] dom G.
Proof.
  induction on wf_env; set solve.
  autorewrite with meta_ext.
  rewrite IHwf_env.
  simpl. fsetdec.
Qed.

Fixpoint typ_struct_measure (T : typ) :=
  match T with
  | typ_top => 1
  | typ_var x => 2
  | typ_fun T U => S $ typ_struct_measure T + typ_struct_measure U
  | typ_all T U => S $ typ_struct_measure T + typ_struct_measure U
  end.

Local Ltac simplify :=
  intros; cbn in *; try lia.

Local Ltac finish :=
  repeat match goal with
         | H : context[forall _, _ = _] |- _ =>
           rewrite H; clear H
         end;
  reflexivity.

Lemma open_typ_same_measure : forall T k u,
    typ_struct_measure $ open_rec_typ k u T = typ_struct_measure T.
Proof.
  induction T; simplify; finish.
Qed.

Lemma typ_struct_measure_ge_1 : forall T,
    typ_struct_measure T >= 1.
Proof. destruct T; routine. Qed.

Definition total (ns : list nat) : nat :=
  fold_right plus 0 ns.

Lemma total_app : forall ns1 ns2,
    total (ns1 ++ ns2) = total ns1 + total ns2.
Proof.
  unfold total.
  induction on list; simpl in *; intros; trivial.
  rewrite IHlist. lia.
Qed.

Definition env_measure (G : env) : nat :=
  total (List.map (fun (tup : var * typ) =>
        let (x, T) := tup in typ_struct_measure T) G).

Lemma env_measure_cons : forall x T G,
    env_measure ((x, T) :: G) = typ_struct_measure T + env_measure G.
Proof. routine. Qed.

Lemma env_measure_app : forall G1 G2,
    env_measure (G2 ++ G1) = env_measure G2 + env_measure G1.
Proof.
  induction G2; simpl; trivial.
  destruct a. rewrite! env_measure_cons.
  rewrite IHG2. lia.
Qed.
  
Arguments env_measure G : simpl never.
Create HintDb measures discriminated.
Hint Rewrite -> env_measure_cons env_measure_app total_app : measures.
Hint Rewrite -> open_typ_same_measure : measures.

Section Predicates.

  Definition is_top (T : typ) :=
    match T with
    | typ_top => True
    | _ => False
    end.

  Definition is_top_dec (T : typ) : {is_top T} + {~is_top T}.
  Proof. destruct T; simpl; auto. Defined.

  Definition is_var (T : typ) :=
    match T with
    | typ_var _ => True
    | _ => False
    end.

  Definition is_var_dec (T : typ) : {A | T = typ_var A } + {~is_var T}.
  Proof. destruct T; simpl; eauto. Defined.
  
  Definition is_fun (T : typ) :=
    match T with
    | typ_fun _ _ => True
    | _ => False
    end.

  Definition is_fun_dec (T : typ) : {S & { U | T = typ_fun S U } } + {~is_fun T}.
  Proof. destruct T; simpl; eauto. Defined.

  Definition is_all (T : typ) :=
    match T with
    | typ_all _ _ => True
    | _ => False
    end.

  Definition is_all_dec (T : typ) : {S & { U | T = typ_all S U } } + {~is_all T}.
  Proof. destruct T; simpl; eauto. Defined.

End Predicates.
