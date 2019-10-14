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

(** * Miscellaneous Definitions

    This file defines well-formedness of contexts, and some structural measures. 
 *)


(** ** Definition of Well-formedness of Contexts *)
Inductive wf_env : env -> Prop :=
(** [――――――――――] Wf-Nil #<br>#
    [wf ⋅]  *)
| wf_nil : wf_env nil
(** [x ∉ fv T ∪ fv G] #<br>#
    [fv T ⊆ dom G] #<br>#
    [wf G] #<br>#
    [――――――――――] Wf-Cons #<br>#
    [wf G ; x : T]  *)
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
  autorewrite with meta_ext. rewrite IHwf_env.
  simpl. fsetdec.
Qed.

(** ** Definition of Structural Measures *)

Fixpoint typ_struct_measure (T : typ) :=
  match T with
  | typ_top => 1
  | typ_bot => 1
  | typ_sel x => 2
  | typ_all T U => S $ typ_struct_measure T + typ_struct_measure U
  | typ_bnd T U => S $ typ_struct_measure T + typ_struct_measure U
  end.

Fixpoint trm_struct_measure (t : trm) :=
  match t with
  | trm_var _ => 1
  | trm_val vl => val_struct_measure vl
  | trm_app _ _ => 1
  | trm_let s t => S $ trm_struct_measure s + trm_struct_measure t
  end
with
val_struct_measure (vl : val) :=
  match vl with
  | val_bnd T => S $ typ_struct_measure T
  | val_lam T t => S $ typ_struct_measure T + trm_struct_measure t
  end.

Local Ltac simplify :=
  intros; cbn in *; try lia.

Local Ltac finish :=
  repeat match goal with
         | H : context[forall _, _ = _] |- _ =>
           rewrite H; clear H
         end;
  reflexivity.

(** The following are properties of the measures. *)
Lemma open_typ_same_measure : forall T k u,
    typ_struct_measure $ open_rec_typ k u T = typ_struct_measure T.
Proof.
  induction T; simplify; finish.
Qed.

Lemma open_trm_same_measure : forall t k u,
    trm_struct_measure $ open_rec_trm k u t = trm_struct_measure t
with
open_val_same_measure : forall vl k u,
    val_struct_measure $ open_rec_val k u vl = val_struct_measure vl.
Proof.
  - induction t; simplify; finish.
  - pose proof open_typ_same_measure.
    induction vl; simplify; finish.
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

(** The measure of a context is just the sum of all measures of the types in it. *)
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

(** The following are predicates to test a type. *)
Section Predicates.

  Definition is_top (T : typ) :=
    match T with
    | typ_top => True
    | _ => False
    end.

  Definition is_top_dec (T : typ) : {is_top T} + {~is_top T}.
  Proof. destruct T; simpl; auto. Defined.

  Definition is_bot (T : typ) :=
    match T with
    | typ_bot => True
    | _ => False
    end.

  Definition is_bot_dec (T : typ) : {is_bot T} + {~is_bot T}.
  Proof. destruct T; simpl; auto. Defined.

  Definition is_sel (T : typ) :=
    match T with
    | typ_sel _ => True
    | _ => False
    end.

  Definition is_sel_dec (T : typ) : {A | T = typ_sel A } + {~is_sel T}.
  Proof. destruct T; simpl; eauto. Defined.

  Definition is_all (T : typ) :=
    match T with
    | typ_all _ _ => True
    | _ => False
    end.

  Definition is_all_dec (T : typ) : {S & { U | T = typ_all S U } } + {~is_all T}.
  Proof. destruct T; simpl; eauto. Defined.
  
  Definition is_bnd (T : typ) :=
    match T with
    | typ_bnd _ _ => True
    | _ => False
    end.

  Definition is_bnd_dec (T : typ) : {S & { U | T = typ_bnd S U } } + {~is_bnd T}.
  Proof. destruct T; simpl; eauto. Defined.

End Predicates.
