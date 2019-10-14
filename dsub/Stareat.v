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
Require Import Misc.
Require Import OpeSub.

From Equations Require Export Equations.

(** * Definitions Related to Stare-at Subtyping

    This file contains definitions related to stare-at subtyping. They include 
    [Revealing], [Upcast], [Downcast] and stare-at subtyping itself.
 *)

Definition subty_measure (G : env) (T : typ) : nat :=
  env_measure G + typ_struct_measure T.
Arguments subty_measure G T/.

Lemma fv_deapp : forall (G1 G2 : env),
    fv G2 [<=] fv (G1 ++ G2).
Proof.
  induction G1; simpl; auto.
  intros. destruct_conjs. specialize (IHG1 G2).
  simpl in *. set simpl in *.
  split; fsetdec.
Qed.

(** ** Definition of [Revealing] *)
Reserved Notation "G1 ⊢ S ⤊ G2 ⊢! U" (at level 90). 
Inductive revealing : env -> typ -> env -> typ -> Prop :=
(** [T is not a path] #<br>#
    [―――――――――――――] Rv-Stop #<br>#
    [G ⊢ T ⤊ G ⊢ T]  *)
| rv_stop : forall G T,
    ~is_sel T ->
    G ⊢ T ⤊ G ⊢! T
(** [―――――――――――――] Rv-Top* #<br>#
    [G ⊢ T ⤊ G ⊢ ⊤]  *)
| rv_top : forall G T,
    G ⊢ T ⤊ nil ⊢! typ_top
(** [G1 ⊢ T ⤊ G1' ⊢ ⊥] #<br>#
    [―――――――――――――――――――――――――――――] Rv-Bot #<br>#
    [G1 ; x : T ; G2 ⊢ x.A ⤊ ⋅ ⊢ ⊥]  *)
| rv_bot : forall G1 G2 G1' T (x : var),
    G1 ⊢ T ⤊ G1' ⊢! typ_bot ->
    G2 ++ x ~ T ++ G1 ⊢ typ_sel (avar_f x) ⤊ nil ⊢! typ_bot
(** [G1 ⊢ T ⤊ G1' ⊢ {A : L .. U}] #<br>#
    [G1' ⊢ U ⤊ G1'' ⊢ U'] #<br>#
    [―――――――――――――――――――――――――――――] Rv-Bot #<br>#
    [G1 ; x : T ; G2 ⊢ x.A ⤊ G1'' ⊢ U']  *)
| rv_bnd : forall G1 G2 T G1' G1'' (x : var) L U U',
    G1 ⊢ T ⤊ G1' ⊢! typ_bnd L U ->
    G1' ⊢ U ⤊ G1'' ⊢! U' ->
    G2 ++ x ~ T ++ G1 ⊢ typ_sel (avar_f x) ⤊ G1'' ⊢! U'
where "G1 ⊢ S ⤊ G2 ⊢! U" := (revealing G1 S G2 U).
Local Hint Constructors revealing.

Local Ltac by_weakening :=
  once ((reassoc 3 with 2 + reassoc 4 with 3); apply weaken_subty; eassumption).

Local Ltac wf_env :=
  lazymatch goal with
  | H : wf_env (_ ++ _) |- _ => apply wf_deapp in H; invert H; subst
  end.    

Local Ltac fv_next := etransitivity; [eassumption |].
Local Ltac fv_shrink := etransitivity; [ | apply fv_deapp].
Local Ltac fv_solve := repeat fv_next; repeat fv_shrink; auto.

(** The following definition is a predicate that asserts the termination of revealing
as an algorithm. *)
Inductive revealing_termination : forall G T G' U,
    G ⊢ T ⤊ G' ⊢! U -> Prop :=
| rt_stop : forall G T
              (not_sel : ~is_sel T),
    revealing_termination (rv_stop G T not_sel)
| rt_top : forall G T,
    revealing_termination (rv_top G T)
| rt_bot : forall G1 G2 G1' T (x : var)
             (Rec : G1 ⊢ T ⤊ G1' ⊢! typ_bot),
    length (G2 ++ x ~ T ++ G1) > length G1 ->
    revealing_termination (rv_bot G2 x Rec)
| rt_bnd : forall G1 G2 T G1' G1'' (x : var) L U U'
             (Rec1 : G1 ⊢ T ⤊ G1' ⊢! typ_bnd L U)
             (Rec2 : G1' ⊢ U ⤊ G1'' ⊢! U'),
    length (G2 ++ x ~ T ++ G1) > length G1 ->
    length (G2 ++ x ~ T ++ G1) > length G1' ->
    revealing_termination (rv_bnd G2 x Rec1 Rec2).

Section RevealingProperties.
  Hint Resolve ope_sub_refl ope_sub_trans ope_sub_nil ope_sub_app.
  
  Theorem revealing_sound : forall G T G' U,
    G ⊢ T ⤊ G' ⊢! U ->
    (G ⊢ T <⦂ U) /\ ~is_sel U /\ (G ⊆<⦂ G').
  Proof.
    induction on revealing.
    all:try lazymatch goal with
            | |- subty (?l2 ++ ?x ~ ?p ++ ?l1) _ _ /\ _ =>
              pose proof (binds_for_sure l2 l1 x p)
            end.
    all:try solve [repeat split; auto].
    all:destruct_conjs.
    - repeat split; auto.
      eapply st_sel2.
      eapply ty_sub. eauto.
      eapply st_trans.
      + by_weakening.
      + instantiate (1 := typ_top). trivial.
    - repeat split; auto.
      + eapply st_sel2.
        eapply ty_sub. eauto.
        eapply st_trans.
        * by_weakening.
        * eapply st_bnd; auto.
          apply ope_narrow_subty with (G' := G1) in H0; trivial.          
          by_weakening.
      + eauto.
  Qed.
    
  Theorem revealing_preserves_wf : forall G T G' U,
      G ⊢ T ⤊ G' ⊢! U ->
      wf_env G ->
      fv T [<=] dom G -> lc T ->
      wf_env G' /\ fv G' [<=] fv G /\ fv U [<=] dom G' /\ lc U.
  Proof.
    induction on revealing; intros.
    1-3:simpl; repeat split; set solve.

    wf_env.
    destruct IHrevealing1; auto.
    pose proof (revealing_sound H3_).
    destruct_conjs.
    destruct IHrevealing2; auto.
    + simpl in *. auto.
    + routine.
    + destruct_conjs. repeat (split; trivial).
      fv_solve.
  Qed.

  Theorem revealing_measure : forall G T G' T',
      G ⊢ T ⤊ G' ⊢! T' ->
      subty_measure G T >= subty_measure G' T'.
  Proof.
    induction on revealing; simpl; try lia.
    - pose proof (typ_struct_measure_ge_1 T).
      lia.
    - simpl in *. autorewrite with measures. 
      lia.
  Qed.
  
  Fixpoint revealing_terminates G S G' U (H : G ⊢ S ⤊ G' ⊢! U) {struct H} :
    revealing_termination H.
  Proof.
    destruct H; constructor;
      repeat rewrite app_length;
      simpl; try lia.
    apply revealing_sound in H.
    destruct_conjs.
    apply ope_sub_length in H2.
    lia.
  Qed.
  
End RevealingProperties.

(** The following is an implementation of Revealing using Equations. *)
Equations reveal_func (G : env) (T : typ) :
  { G' : env & { T' : typ | length G' <= length G } } by wf (length G) lt :=
  {
      reveal_func G T with is_sel_dec T => {
      | inleft (exist _ (avar_b _) _) => existT _ nil (exist _ typ_top _);
      | inleft (exist _ (avar_f x) _) with split_at x G => {
        | None => existT _ nil (exist _ typ_top _);
        | Some (existT _ T' (existT _ G1 _)) with reveal_func G1 T' => {
          | existT _ G1' (exist _ U _) with U => {
            | typ_bot => existT _ nil (exist _ typ_bot _);
            | typ_bnd _ U' with reveal_func G1' U' => {
              | existT _ G1'' (exist _ T'' _) => existT _ G1'' (exist _ T'' _)
              };
            | _ => existT _ nil (exist _ typ_top _)
            }
          }
        };
      | inright _ => existT _ G (exist _ T _)
      }
  }.

Local Ltac eval_obli := repeat rewrite app_length; simpl; lia.
Next Obligation. eval_obli. Qed.
Next Obligation. eval_obli. Qed.
Next Obligation. eval_obli. Qed.
Next Obligation. eval_obli. Qed.
Next Obligation. eval_obli. Qed.
Next Obligation. eval_obli. Qed.
Next Obligation. eval_obli. Qed.
Next Obligation. eval_obli. Qed.
Next Obligation. eval_obli. Qed.

Theorem reveal_func_sound_wrt_spec : forall G T G' T' pf,
    reveal_func G T = existT _ G' (exist _ T' pf) ->
    G ⊢ T ⤊ G' ⊢! T'.
Proof.
  intros. funelim (reveal_func G T).
  all:rewrite <- Heqcall in *; progressive_inversions; auto.
  - tidy_up. eapply rv_bot. eauto.
  - tidy_up. eapply rv_bnd; eauto.
Qed.

(** ** Definition of [Upcast]

    The actual predicate is on variable because Upcast only applies to path dependent
 types, and thus only variables can vary.
  *)
Reserved Notation "G1 ⊢ S ↗ G2 ⊢! U" (at level 90). 
Inductive upcast : env -> avar -> env -> typ -> Prop :=
(** [―――――――――――――――] U-Top* #<br>#
    [G ⊢ x.A ↗ ⋅ ⊢ ⊤] *)
| uc_top : forall G x,
    G ⊢ x ↗ nil ⊢! typ_top
(** [G1 ⊢ T ⤊ G1' ⊢! ⊥] #<br>#
    [―――――――――――――――――――――――――――――] U-Bot #<br>#
    [G1 ; x : T ; G2 ⊢ x.A ↗ ⋅ ⊢ ⊥] *)
| uc_bot : forall G1 G2 x T G1',
    G1 ⊢ T ⤊ G1' ⊢! typ_bot ->
    G2 ++ x ~ T ++ G1 ⊢ avar_f x ↗ nil ⊢! typ_bot
(** [G1 ⊢ T ⤊ G1' ⊢! {A : L .. U}] #<br>#
    [―――――――――――――――――――――――――――――――] U-Bnd #<br>#
    [G1 ; x : T ; G2 ⊢ x.A ↗ G1' ⊢ U] *)
| uc_bnd : forall G1 G2 x T G1' L U,
    G1 ⊢ T ⤊ G1' ⊢! typ_bnd L U ->
    G2 ++ x ~ T ++ G1 ⊢ avar_f x ↗ G1' ⊢! U
where "G1 ⊢ S ↗ G2 ⊢! U" := (upcast G1 S G2 U).
Local Hint Constructors upcast.

Section UpcastProperties.
  
  Theorem upcast_decreases_measure : forall G x G' U,
    G ⊢ x ↗ G' ⊢! U ->
    subty_measure G (typ_sel x) > subty_measure G' U.
  Proof.
    destr on upcast; simpl;
      autorewrite with measures; try lia.
    apply revealing_measure in H.
    simpl in *. lia.
  Qed.

  Hint Resolve ope_sub_refl ope_sub_nil ope_sub_trans ope_sub_app.
  Hint Constructors ope_sub.

  Theorem upcast_sound : forall G x G' U,
      G ⊢ x ↗ G' ⊢! U ->
      (G ⊢ typ_sel x <⦂ U) /\ (G ⊆<⦂ G').
  Proof.
    destr on upcast.
    all:try lazymatch goal with
            | |- subty (?l2 ++ ?x ~ ?p ++ ?l1) _ _ /\ _ =>
              pose proof (binds_for_sure l2 l1 x p)
            end.
    all:routine.
    - eapply st_sel2.
      apply revealing_sound in H. destruct_conjs.
      eapply ty_sub. eauto.
      eapply st_trans.
      + simpl_env. by_weakening.
      + instantiate (1 := typ_top). trivial.
    - eapply st_sel2.
      apply revealing_sound in H. destruct_conjs.
      eapply ty_sub. eauto.
      by_weakening.
    - apply revealing_sound in H. destruct_conjs.
      eauto.
  Qed.

  Hint Resolve wf_nil fv_deapp.

  Theorem upcast_preserves_wf : forall G x G' U,
      G ⊢ x ↗ G' ⊢! U ->
      wf_env G ->
      fv x [<=] dom G ->
      wf_env G' /\ fv G' [<=] fv G /\ fv U [<=] dom G' /\ lc U.
  Proof.
    destr on upcast; intros.
    1-2:simpl; repeat split; set solve.

    wf_env.
    apply revealing_preserves_wf in H; trivial.
    destruct_conjs.
    repeat split; trivial.
    - fv_solve.
    - simpl in *. auto.
    - routine.    
  Qed.

  (** The following is an implementation of Upcast. *)
  Definition upcast_func (G : env) (x : avar) : env * typ :=
    match x with
    | avar_b _ => (nil, typ_top)
    | avar_f x =>
      match split_at x G with
      | None => (nil, typ_top)
      | Some (existT _ T (existT _ G1 _)) =>
        let '(existT _ G1' (exist _ U _)) := reveal_func G1 T in
        match U with
        | typ_bot => (nil, typ_bot)
        | typ_bnd _ U' =>
          (G1', U')
        | _ => (nil, typ_top)
        end
      end
    end.

  Theorem upcast_func_sound_wrt_spec : forall G x G' T,
      upcast_func G x = (G', T) ->
      G ⊢ x ↗ G' ⊢! T.
  Proof.
    intros. unfold upcast_func in H.
    execute H.
    all:progressive_inversions; auto.
    - apply reveal_func_sound_wrt_spec in Heqs2.
      tidy_up. eapply uc_bot. eauto.
    - apply reveal_func_sound_wrt_spec in Heqs2.
      tidy_up. eapply uc_bnd; eauto.
  Qed.
  
  Lemma upcast_func_decreases_measure : forall G x G' T,
      upcast_func G x = (G', T) ->
      subty_measure G (typ_sel x) > subty_measure G' T.
  Proof.
    intros. apply upcast_func_sound_wrt_spec in H.
    apply upcast_decreases_measure. trivial.
  Qed.
  
  Definition upcast_f_u G (x : avar) (tup : env * typ)
             (H : upcast_func G x = tup) :
    { G'' & {T'' |
             subty_measure G (typ_sel x) > subty_measure G'' T'' } }.
  Proof.
    refine (existT _ (fst tup) (exist _ (snd tup) _)).
    abstract (destruct tup; simpl fst; simpl snd;
              apply upcast_func_decreases_measure; trivial).
  Defined.

  Lemma upcast_f_u_eq : forall G x tup pf G'' T'' pf',
      @upcast_f_u G x tup pf = existT _ G'' (exist _ T'' pf') ->
      G'' = fst tup /\ T'' = snd tup.
  Proof.
    intros. unfold upcast_f_u in H. tidy_up.
    auto.
  Qed.
  
  Definition upcast_f_dep (G : env) (x : avar) : 
    { G' & {T' |
            subty_measure G (typ_sel x) > subty_measure G' T' } }
    := @upcast_f_u G x (upcast_func G x) eq_refl.
  
  Lemma upcast_f_dep_eq_upcast_f : forall G x G' T' pf,
      upcast_f_dep G x = existT _ G' (exist _ T' pf) ->
      upcast_func G x = (G', T').
  Proof.
    intros. unfold upcast_f_dep in H.
    apply upcast_f_u_eq in H.
    destruct (upcast_func G x); tidy_up.
    auto.
  Qed.

End UpcastProperties.


(** ** Definition of [Downcast]

    The definition is very symmetric to the one of Upcast.
 *)
Reserved Notation "G1 ⊢ S ↘ G2 ⊢! U" (at level 90). 
Inductive downcast : env -> avar -> env -> typ -> Prop :=
(** [―――――――――――――――] D-Bot* #<br>#
    [G ⊢ x.A ↘ ⋅ ⊢ ⊥] *)
| dc_bot : forall G x,
    G ⊢ x ↘ nil ⊢! typ_bot
(** [G1 ⊢ T ⤊ G1' ⊢! ⊥] #<br>#
    [―――――――――――――――――――――――――――――] D-Top #<br>#
    [G1 ; x : T ; G2 ⊢ x.A ↘ ⋅ ⊢ ⊤] *)
| dc_top : forall G1 G2 x T G1',
    G1 ⊢ T ⤊ G1' ⊢! typ_bot ->
    downcast (G2 ++ x ~ T ++ G1) (avar_f x) nil typ_top
(** [G1 ⊢ T ⤊ G1' ⊢! {A : L .. U}] #<br>#
    [―――――――――――――――――――――――――――――――] D-Bnd #<br>#
    [G1 ; x : T ; G2 ⊢ x.A ↘ G1' ⊢ L] *)
| dc_bnd : forall G1 G2 x T G1' L U,
    revealing G1 T G1' (typ_bnd L U) ->
    downcast (G2 ++ x ~ T ++ G1) (avar_f x) G1' L
where "G1 ⊢ S ↘ G2 ⊢! U" := (downcast G1 S G2 U). 
Local Hint Constructors downcast.

Section DowncastProperties.
  
  Theorem downcast_decreases_measure : forall G x G' U,
    G ⊢ x ↘ G' ⊢! U ->
    subty_measure G (typ_sel x) > subty_measure G' U.
  Proof.
    destr on downcast; simpl;
      autorewrite with measures; try lia.
    apply revealing_measure in H.
    simpl in *. lia.
  Qed.

  Hint Resolve ope_sub_refl ope_sub_nil ope_sub_trans ope_sub_app.
  Hint Constructors ope_sub.

  Theorem downcast_sound : forall G x G' U,
      G ⊢ x ↘ G' ⊢! U ->
      (G ⊢ U <⦂ typ_sel x) /\ (G ⊆<⦂ G').
  Proof.
    destr on downcast.
    all:try lazymatch goal with
            | |- subty (?l2 ++ ?x ~ ?p ++ ?l1) _ _ /\ _ =>
              pose proof (binds_for_sure l2 l1 x p)
            end.
    all:routine.
    - eapply st_sel1.
      apply revealing_sound in H. destruct_conjs.
      eapply ty_sub. eauto.
      eapply st_trans.
      + simpl_env. by_weakening.
      + instantiate (1 := typ_top). trivial.
    - eapply st_sel1.
      apply revealing_sound in H. destruct_conjs.
      eapply ty_sub. eauto.
      by_weakening.
    - apply revealing_sound in H. destruct_conjs.
      eauto.
  Qed.

  Hint Resolve wf_nil fv_deapp.
  
  Theorem downcast_preserves_wf : forall G x G' U,
      G ⊢ x ↘ G' ⊢! U ->
      wf_env G ->
      fv x [<=] dom G ->
      wf_env G' /\ fv G' [<=] fv G /\ fv U [<=] dom G' /\ lc U.
  Proof.
    destr on downcast; intros.
    1-2:simpl; repeat split; set solve.

    wf_env.
    apply revealing_preserves_wf in H; trivial.
    destruct_conjs.
    repeat split; trivial.
    - fv_solve.
    - simpl in *. auto.
    - routine.    
  Qed.

  (** The following is an implementation of Downcast. *)
  Definition downcast_func (G : env) (x : avar) : env * typ :=
    match x with
    | avar_b _ => (nil, typ_bot)
    | avar_f x =>
      match split_at x G with
      | None => (nil, typ_bot)
      | Some (existT _ T (existT _ G1 _)) =>
        let '(existT _ G1' (exist _ U _)) := reveal_func G1 T in
        match U with
        | typ_bot => (nil, typ_top)
        | typ_bnd L _ =>
          (G1', L)
        | _ => (nil, typ_bot)
        end
      end
    end.

  Theorem downcast_func_sound_wrt_spec : forall G x G' T,
      downcast_func G x = (G', T) ->
      downcast G x G' T.
  Proof.
    intros. unfold downcast_func in H.
    execute H.
    all:progressive_inversions; auto.
    - apply reveal_func_sound_wrt_spec in Heqs2.
      tidy_up. eapply dc_top. eauto.
    - apply reveal_func_sound_wrt_spec in Heqs2.
      tidy_up. eapply dc_bnd; eauto.
  Qed.
  
  Lemma downcast_func_decreases_measure : forall G x G' T,
      downcast_func G x = (G', T) ->
      subty_measure G (typ_sel x) > subty_measure G' T.
  Proof.
    intros. apply downcast_func_sound_wrt_spec in H.
    apply downcast_decreases_measure. trivial.
  Qed.
  
  Definition downcast_f_u G (x : avar) (tup : env * typ)
             (H : downcast_func G x = tup) :
    { G'' & {T'' |
             subty_measure G (typ_sel x) > subty_measure G'' T'' } }.
  Proof.
    refine (existT _ (fst tup) (exist _ (snd tup) _)).
    abstract (destruct tup; simpl fst; simpl snd;
              apply downcast_func_decreases_measure; trivial).
  Defined.

  Lemma downcast_f_u_eq : forall G x tdown pf G'' T'' pf',
      @downcast_f_u G x tdown pf = existT _ G'' (exist _ T'' pf') ->
      G'' = fst tdown /\ T'' = snd tdown.
  Proof.
    intros. unfold downcast_f_u in H. tidy_up.
    auto.
  Qed.
  
  Definition downcast_f_dep (G : env) (x : avar) : 
    { G' & {T' |
            subty_measure G (typ_sel x) > subty_measure G' T' } }
    := @downcast_f_u G x (downcast_func G x) eq_refl.
  
  Lemma downcast_f_dep_eq_downcast_f : forall G x G' T' pf,
      downcast_f_dep G x = existT _ G' (exist _ T' pf) ->
      downcast_func G x = (G', T').
  Proof.
    intros. unfold downcast_f_dep in H.
    apply downcast_f_u_eq in H.
    destruct (downcast_func G x); tidy_up.
    auto.
  Qed.

End DowncastProperties.

(* Arguments upcast_f_dep G x/. *)
(* Arguments downcast_f_dep G x/. *)
(* Arguments upcast_f_u G x tup H/. *)
(* Arguments downcast_f_u G x tup H/. *)

(** ** Definition of Stare-at Subtyping *)
Reserved Notation "[ L ] G1 >> T '<⦂' U << G2" (at level 70).
Inductive stareat : atoms -> env -> typ -> typ -> env -> Prop :=
(** [――――――――――――――――] SA-Bot #<br>#
    [G1 ≫ ⊥ <: T ≪ G2] *)
| sa_bot : forall L G1 T G2, [ L ] G1 >> typ_bot <⦂ T << G2
(** [――――――――――――――――] SA-Top #<br>#
    [G1 ≫ T <: ⊤ ≪ G2] *)
| sa_top : forall L G1 T G2, [ L ] G1 >> T <⦂ typ_top << G2
(** [――――――――――――――――――――] SA-VRefl #<br>#
    [G1 ≫ x.A <: x.A ≪ G2] *)
| sa_sel_refl : forall L G1 x G2, [ L ] G1 >> typ_sel x <⦂ typ_sel x << G2
(** [G1 ⊢ x.A ↗ G1' ⊢ T] #<br>#
    [G1' ≫ T <: U ≪ G2] #<br>#
    [――――――――――――――――――] SA-Sel2 #<br>#
    [G1 ≫ x.A <: U ≪ G2] *)
| sa_sel_left : forall L G1 x G2 T U G1',
    G1 ⊢ x ↗ G1' ⊢! T ->
    [ L ] G1' >> T <⦂ U << G2 ->
    [ L ] G1 >> typ_sel x <⦂ U << G2
(** [G2 ⊢ x.A ↘ G2' ⊢ U] #<br>#
    [G1 ≫ T <: U ≪ G2'] #<br>#
    [――――――――――――――――――] SA-Sel1 #<br>#
    [G1 ≫ T <: x.A ≪ G2] *)
| sa_sel_right : forall L G1 x G2 T U G2',
    G2 ⊢ x ↘ G2' ⊢! U ->
    [ L ] G1 >> T <⦂ U << G2' ->
    [ L ] G1 >> T <⦂ typ_sel x << G2

(** [G1 ≫ T2 >: T1 ≪ G2'] #<br>#
    [G1 ; x : T1 ≫ U1 <: U2 ≪ G2 ; x : T2] #<br>#
    [――――――――――――――――――――――――――――――――――――] SA-All #<br>#
    [G1 ≫ ∀(x : T1)U1 <: ∀(x : T2)U2 ≪ G2] *)
| sa_all : forall L G1 T1 U1 G2 T2 U2 x,
    x `notin` fv G1 `union` fv T1 `union` fv T2
      `union` fv U1 `union` fv U2 `union` fv G2 `union` L ->
    [ L ] G2 >> T2 <⦂ T1 << G1 ->
    [ L  `union` singleton x `union` fv T2 ]
      x ~ T1 ++ G1 >> open x U1 <⦂ open x U2 << x ~ T2 ++ G2 ->
    [ L ] G1 >> typ_all T1 U1 <⦂ typ_all T2 U2 << G2
(** [G1 ≫ S2 >: S1 ≪ G2] #<br>#
    [G1 ≫ U1 <: U2 ≪ G2] #<br>#
    [――――――――――――――――――――――――――――――――――――] SA-Bnd #<br>#
    [G1 ≫ {A : S1 .. U1} <: {A : S2 .. U2} ≪ G2] *)
| sa_bnd : forall L G1 S1 U1 S2 U2 G2,
    [ L ] G2 >> S2 <⦂ S1 << G1 ->
    [ L ] G1 >> U1 <⦂ U2 << G2 ->
    [ L ] G1 >> typ_bnd S1 U1 <⦂ typ_bnd S2 U2 << G2
where "[ L ] G1 >> T '<⦂' U << G2" := (stareat L G1 T U G2)%type.
Local Hint Constructors stareat.

Definition bsubtyp (G : env) (T U : typ) : Prop :=
  uniq G /\ [ fv G ] G >> T <⦂ U << G.
Arguments bsubtyp G T U/.

Notation "G ⊢S T <⦂ U" := (bsubtyp G T U)%type (at level 70).

Section BiSubtyProperties.

  Hint Resolve ope_sub_trans.
  
  Theorem ope_sub_stareat_sound : forall L G1 T U G2,
    [ L ] G1 >> T <⦂ U << G2 ->
    forall G,
      fv G [<=] L ->
      uniq G ->
      G ⊆<⦂ G1 ->
      G ⊆<⦂ G2 ->
      G ⊢ T <⦂ U.
  Proof.
    induction on stareat; intros; auto.
    - apply upcast_sound in H. destruct_conjs.
      eapply st_trans.
      + eapply ope_narrow_subty; eassumption.
      + apply IHstareat; eauto.
    - apply downcast_sound in H. destruct_conjs.
      eapply st_trans.
      + apply IHstareat; eauto.
      + eapply ope_narrow_subty; eassumption.

    - eapply st_all; auto.
      assert (x `notin` fv G). {
        eapply notin_subset_relax. eassumption. auto.
      }
      cofinite. apply open_subst_subty with (x := x); trivial.
      + repeat (apply notin_union_3; auto).
      + auto.
      + apply IHstareat2.
        * assert (fv (x ~ T2 ++ G) [=] singleton x `union` fv G `union` fv T2). {
             simpl. set solve.
           }
           rewrite H5. set solve.
        * routine.
        * apply os_keep; auto.
        * apply os_keep; auto.
  Qed.

  Program Fixpoint stareat_refl (T : typ) {measure (typ_struct_measure T)}
    : forall L G1 G2,
      [ L ] G1 >> T <⦂ T << G2 := _.
  Next Obligation.
    destruct T; auto.
    - pick_fresh x. econstructor.
      + eauto.
      + eapply stareat_refl; eauto.
        simpl. lia.
      + eapply stareat_refl; eauto.
        rewrite open_typ_same_measure. simpl. lia.
    - constructor; eapply stareat_refl; eauto.
      all:simpl; lia.
  Qed.

End BiSubtyProperties.

Definition eq_typ_sel (x : avar) (y : avar)
  : {x = y} + {x <> y}.
Proof.
  destruct (x == y); subst; eauto.
Defined.

Local Hint Resolve ope_sub_refl.

Theorem bsubtyp_sound : forall G T U,
    G ⊢S T <⦂ U ->
    G ⊢ T <⦂ U.
Proof.
  simpl. intros. tidy_up.
  eapply ope_sub_stareat_sound; eauto.
Qed.

(** ** Termination of Stare-at Subtyping *)

(** The following is a predicate of termination of stare-at subtyping. *)
Inductive stareat_termination : forall L G1 S U G2, [ L ] G1 >> S <⦂ U << G2 -> Prop :=
| bt_bot : forall L G1 T G2, stareat_termination (sa_bot L G1 T G2)
| bt_top : forall L G1 T G2, stareat_termination (sa_top L G1 T G2)
| bt_sel_refl : forall L G1 x G2, stareat_termination (sa_sel_refl L G1 x G2)
| bt_sel_left : forall L G1 x G2 T U G1'
                  (Uc : upcast G1 x G1' T)
                  (Rec : [ L ] G1' >> T <⦂ U << G2),
    subty_measure G1' T + subty_measure G2 U <
    subty_measure G1 (typ_sel x) + subty_measure G2 U ->
    stareat_termination (sa_sel_left Uc Rec)
| bt_sel_right : forall L G1 x G2 T U G2'
                   (Dc : downcast G2 x G2' U)
                   (Rec : [ L ] G1 >> T <⦂ U << G2'),
    subty_measure G1 T + subty_measure G2' U <
    subty_measure G1 T + subty_measure G2 (typ_sel x) ->
    stareat_termination (sa_sel_right Dc Rec)

| bt_all : forall L G1 T1 U1 G2 T2 U2 x
             (F : x `notin` fv G1 `union` fv T1 `union` fv T2
                   `union` fv U1 `union` fv U2 `union` fv G2 `union` L)
             (Rec1 : [ L ] G2 >> T2 <⦂ T1 << G1)
             (Rec2 : [ L  `union` singleton x `union` fv T2 ]
                       x ~ T1 ++ G1 >> open x U1 <⦂ open x U2 << x ~ T2 ++ G2),
    subty_measure G2 T2 + subty_measure G1 T1 <
    subty_measure G1 (typ_all T1 U1) + subty_measure G2 (typ_all T2 U2) ->
    subty_measure (x ~ T1 ++ G1) (open x U1) + subty_measure (x ~ T2 ++ G2) (open x U2) <
    subty_measure G1 (typ_all T1 U1) + subty_measure G2 (typ_all T2 U2) ->
    stareat_termination (sa_all U1 U2 F Rec1 Rec2)
| bt_bnd : forall L G1 S1 U1 S2 U2 G2
             (Rec1 : [ L ] G2 >> S2 <⦂ S1 << G1)
             (Rec2 : [ L ] G1 >> U1 <⦂ U2 << G2),
    subty_measure G2 S2 + subty_measure G1 S1 <
    subty_measure G1 (typ_bnd S1 U1) + subty_measure G2 (typ_bnd S2 U2) ->
    subty_measure G1 U1 + subty_measure G2 U2 <
    subty_measure G1 (typ_bnd S1 U1) + subty_measure G2 (typ_bnd S2 U2) ->
    stareat_termination (sa_bnd Rec1 Rec2).
Local Hint Constructors stareat_termination.

(** One can compare this termination proof with the one in #<a
href="Step.html">Step.v</a># and see how the setup of [Revealing] has shortened the
proof drastically. *)
Section Termination.
  Hint Rewrite -> open_typ_same_measure : measures.
  
  Fixpoint stareat_terminates L G1 S U G2
           (D : [ L ] G1 >> S <⦂ U << G2) {struct D} :
    stareat_termination D.
  Proof.
    destruct D; constructor;
      lazymatch goal with
      | H : upcast _ _ _ _ |- _ =>
        apply upcast_decreases_measure in H
      | H : downcast _ _ _ _ |- _ =>
        apply downcast_decreases_measure in H
      | _ => idtac
      end;
      simpl in *; auto; try lia.

    autorewrite with measures.
    lia.
  Qed.

End Termination.
