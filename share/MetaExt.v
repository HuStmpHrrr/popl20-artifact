Set Implicit Arguments.
Require Import LibUtils.
Require Export Metalib.Metatheory.
Import AtomSetProperties.
Import AtomSetImpl.

Ltac atoms_in_env :=
  let L := gather_atoms in
  let L' := beautify_fset L in exact L'.

Definition fresh_vars (vs : vars) : {v | v `notin` vs}.
Proof.
  pose proof (atom_fresh_for_list (AtomSetImpl.elements vs)).
  destruct H.
  exists x. rewrite <- CoqListFacts.InA_iff_In in n.
  intro Contra. apply n.
  apply AtomSetImpl.elements_1. trivial.
Defined.

Notation pick_fresh_var := (fresh_vars ltac:(atoms_in_env)).

Create HintDb meta_ext discriminated.

Ltac set_solve n := auto n with meta_ext core.
Ltac eset_solve n := eauto n with meta_ext core.

Tactic Notation "set" "simpl" := autorewrite with meta_ext.
Tactic Notation "set" "simpl" "in" "*" := autorewrite with meta_ext in *.

Tactic Notation "set" "solve" int(n) := set_solve n.
Tactic Notation "set" "solve" := set solve 5.

Lemma union_or_equiv :
  forall x s1 s2, x `in` union s1 s2 <-> x `in` s1 \/ x `in` s2.
Proof.
  intros. split; intros.
  - apply union_1. trivial.
  - destruct H.
    + apply union_2. trivial.
    + apply union_3. trivial.
Qed.

Ltac rewrite_in :=
  repeat rewrite union_or_equiv in *.

Ltac solve_in :=
  lazymatch goal with
    |- ?x `in` _ =>
    repeat match goal with
           | H : x `in` union _ _ |- _ =>
             rewrite union_or_equiv in H; destruct H
           end;
    repeat rewrite union_or_equiv;
    auto
  end.

Lemma empty_is_empty : Empty empty.
Proof. apply empty_is_empty_2. apply equal_refl. Qed.

Hint Resolve empty_is_empty : meta_ext.
Hint Resolve equal_refl : meta_ext.

Lemma union_empty_1 :
  forall s, union s empty [=] s.
Proof.
  intros. rewrite empty_union_2; set solve.
Qed.

Hint Resolve union_empty_1 : meta_ext.

Lemma union_empty_2 :
  forall s, union empty s [=] s.
Proof.
  intros. rewrite union_sym. set solve.
Qed.

Hint Resolve union_empty_2 : meta_ext.
Hint Rewrite -> union_empty_1 union_empty_2 : meta_ext.

Hint Resolve subset_empty : meta_ext.
Hint Resolve subset_refl : meta_ext.
Hint Resolve union_subset_1 : meta_ext.
Hint Resolve union_subset_2 : meta_ext.
Hint Unfold AtomSetImpl.Subset : meta_ext core.

Hint Extern 1 (_ `in` _) => solve_in : meta_ext.

Lemma union_trans_proof : forall s s1 s2,
    s [<=] s2 -> s [<=] union s1 s2.
Proof.
  intros. etransitivity.
  eassumption.
  set solve.
Qed.

Lemma notin_subset_relax : forall x s1 s2,
    s1 [<=] s2 ->
    x `notin` s2 ->
    x `notin` s1.
Proof.
  intros. intro Contra.
  apply H0. eapply in_subset; eassumption.
Qed.

Lemma union_empty_3 : forall s1 s2,
    union s1 s2 [=] empty -> s1 [=] empty /\ s2 [=] empty.
Proof.
  intros. unfold AtomSetImpl.Equal in *. split.
  - split; intros.
    + apply H. set solve.
    + exfalso. eapply empty_iff. eassumption.
  - split; intros.
    + apply H. set solve.
    + exfalso. eapply empty_iff. eassumption.
Qed.

Lemma union_empty_rewrite : forall s1 s2,
    union s1 s2 [=] empty <-> s1 [=] empty /\ s2 [=] empty.
Proof.
  split. apply union_empty_3.
  intros. destruct H.
  rewrite H. rewrite H0. set solve.
Qed.
Hint Rewrite -> union_empty_rewrite : meta_ext.

Ltac solve_subset :=
  let rec doit lhs rhs :=
      lazymatch rhs with
      | union ?y ?z =>
        lazymatch y with
        | lhs => apply union_subset_1
        | _ => apply union_trans_proof; doit lhs z
        end
      | lhs => apply Subset_refl
      end in
  repeat rewrite union_assoc;
  repeat apply union_subset_3;
  lazymatch goal with
  | |- ?x [<=] ?y => doit x y
  end.

Hint Extern 1 (_ [<=] _) => solve_subset : meta_ext.
Hint Rewrite -> AtomSetProperties.add_union_singleton : meta_ext.

Ltac set_solve n ::=
  try solve [simpl in *; set simpl in *; destruct_conjs; auto n with meta_ext core].
Ltac eset_solve n ::=
  try solve [simpl in *; set simpl in *; destruct_conjs; eauto n with meta_ext core].

Lemma lnot_get : forall T lab (l : list (label * T)),
    lget lab l = None -> ~lIn lab (ldom l).
Proof. induction on list; routine. Qed.

Lemma get_to_binds : forall T (l : list (var * T)) x r,
    get x l = Some r -> binds x r l.
Proof using.
  induction l; routine.
  right. apply IHl. trivial.
Defined.

Lemma binds_to_get : forall T (l : list (var * T)) x r,
    binds x r l -> uniq l -> get x l = Some r.
Proof using.
  induction on list; routine.
  exfalso. apply H7. eapply binds_In.
  eassumption.
Defined.

Definition get_witness {A : Type} (v : var) (l : list (var * A)) :
  forall r, get v l = Some r -> { l1 & { l2 | l1 ++ v ~ r ++ l2 = l } }.
Proof using.
  induction l; intros; simpl in *.
  - congruence.
  - destruct_conjs.
    destruct (v == a).
    + progressive_inversions.
      exists nil. eexists. simpl; trivial.
    + apply IHl in H. destruct_conjs.
      do 2 eexists. rewrite <- H0.
      reassoc 4 with 2. reflexivity.
Defined.

Definition get_for_sure : forall T (l : list (var * T)) x,
    x `in` dom l -> { r | get x l = Some r }.
Proof using.
  induction l.
  - routine. exfalso. revert H.
    lazymatch goal with |- ?G => change G with (x `notin` empty) end.
    auto.
  - eroutine.
    apply IHl.
    apply AtomSetImpl.add_3 with a; trivial.
    congruence.
Qed.

Fixpoint split_at {A} (x : var) (l : list (var * A))
  : option { r & {l1 & { l2 | l = l2 ++ x ~ r ++ l1 } } }.
Proof.
  refine (match l with
          | nil => None
          | cons (y, r) l' =>
            if x == y then Some (existT _ r (existT _ l' (exist _ nil _)))
            else match split_at _ x l' with
                 | None => None
                 | Some (existT _ r' (existT _ l2 (exist _ l1 _))) =>
                   Some (existT _ r' (existT _ l2 (exist _ (y ~ r ++ l1) _)))
                 end
          end).
  all:abstract (subst; reflexivity).
Defined.

Lemma binds_witness : forall T (l : list (var * T)) x r,
    binds x r l ->
    exists l1 l2, l = l1 ++ x ~ r ++ l2.
Proof.
  induction l; routine.
  - exists nil, l. trivial.
  - apply IHl in H. tidy_up.
    exists ((a, t0) :: H), H0. trivial.
Qed.

Lemma in_witness : forall T (l : list (var * T)) x,
    x `in` dom l ->
         exists r l1 l2, l = l1 ++ x ~ r ++ l2.
Proof.
  intros. apply get_for_sure in H.
  tidy_up. apply get_to_binds in H0.
  apply binds_witness in H0.
  eroutine.
Qed.

Lemma lget_to_lbinds : forall T (l : list (label * T)) x r,
    lget x l = Some r -> lbinds x r l.
Proof using.
  induction l; routine.
  right. apply IHl. trivial.
Defined.

Lemma lbinds_to_lget : forall T (l : list (label * T)) x r,
    lbinds x r l -> luniq l -> lget x l = Some r.
Proof using.
  induction on list; routine.
  exfalso. apply H7. eapply LabelAssocList.binds_In.
  eassumption.
Defined.

Definition lget_witness {A : Type} (v : label) (l : list (label * A)) :
  forall r, lget v l = Some r -> { l1 & { l2 | l1 ++ v ~ r ++ l2 = l } }.
Proof using.
  induction l; intros; simpl in *.
  - congruence.
  - destruct_conjs.
    destruct (v == l0).
    + progressive_inversions.
      exists nil. eexists. simpl; trivial.
    + apply IHl in H. destruct_conjs.
      do 2 eexists. rewrite <- H0.
      reassoc 4 with 2. reflexivity.
Defined.

Definition lget_for_sure : forall T (l : list (label * T)) x,
    lIn x (ldom l) -> { r | lget x l = Some r }.
Proof using.
  induction l.
  - routine. exfalso. revert H.
    lazymatch goal with |- ?G => change G with (x `lnotin` lempty) end.
    auto.
  - intros. simpl. destruct a.
    change (x == l0) with (Label.eq_dec x l0).
    destruct (Label.eq_dec x l0).
    eroutine.
    apply IHl.
    apply LabelSetImpl.add_3 with l0; trivial.
    congruence.
Qed.

Lemma lget_not_in_ldom : forall {A} (l : list (label * A)) a,
    lget a l = None -> a `lnotin` ldom l.
Proof. induction on list; routine. Qed.


Definition get_app : forall {T} {l1 l2 : list (var * T)} {x v},
    get x (l1 ++ l2) = Some v ->
    {get x l1 = Some v} + {get x l2 = Some v /\ x `notin` dom l1}.
Proof.
  induction l1; routine.
  edestruct IHl1; routine.
Defined.

Definition get_uniq_app : forall {T} {l1 l2 : list (var * T)} {x v},
    uniq (l1 ++ l2) ->
    get x (l1 ++ l2) = Some v ->
    {get x l1 = Some v /\ x `notin` dom l2} + {get x l2 = Some v /\ x `notin` dom l1}.
Proof.
  intros. destruct (get_app H0); auto.
  left; split; auto.
  eapply fresh_app_r. eassumption.
  apply get_to_binds. eassumption.
Defined.

Theorem union_conj : forall s1 s2 s,
    union s1 s2 [<=] s <-> s1 [<=] s /\ s2 [<=] s.
Proof.
  split; intros; set solve.
Qed.
Hint Rewrite -> union_conj : meta_ext.

Lemma In_is_in : forall x l,
    List.In x l <->
    x `in` AtomSetProperties.of_list l.
Proof.
  intros. rewrite AtomSetProperties.of_list_1.
  rewrite InA_iff_In. reflexivity.
Qed.
Hint Rewrite -> In_is_in : meta_ext.

Lemma disjoined_singleton : forall x s1 s2,
    s1 [<=] union (singleton x) s2 ->
    x `notin` s1 ->
    s1 [<=] s2.
Proof.
  intros. tidy_up. intros.
  specialize (H _ H1).
  apply union_1 in H.
  destruct H; trivial.
  apply singleton_1 in H. subst.
  contradiction.
Qed.

Lemma in_subset_singleton : forall x s,
    x `in` s <->
    singleton x [<=] s.
Proof.
  split; intros.
  - intro y; intros.
    apply singleton_1 in H0.
    subst. trivial.
  - apply H. apply singleton_2. trivial.
Qed.
Hint Rewrite -> in_subset_singleton : meta_ext.

Lemma exclude_add : forall x y s,
    singleton x [<=] add y s ->
    x <> y ->
    singleton x [<=] s.
Proof.
  intros. set simpl in *.
  eapply disjoined_singleton; try eassumption.
  intro Contra. apply H0. 
  apply AtomSetImpl.singleton_1. trivial.
Qed.

Hint Rewrite -> dom_cons dom_app union_assoc : meta_ext.

Lemma add_empty_noteq : forall x s,
    ~ add x s [=] empty.
Proof.
  intros. intro Contra.
  assert (x `in` add x s) by auto.
  rewrite Contra in H.
  revert H. tidy_up.
  auto.
Qed.
