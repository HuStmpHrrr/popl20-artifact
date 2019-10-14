Set Implicit Arguments.
Require Import LibUtils.
Require Import Metalib.Metatheory.
Require Import MetaExt.
Require Import Lia.
Require Import Coq.Program.Wf.
Require Import Lexicographic_Product.
Require Import Coq.Relations.Relation_Operators.
Require Import Coq.Arith.Wf_nat.
Require Import ListRelations.

Lemma notin_neq : forall A (l : list A) x y,
    In x l ->
    ~ In y l ->
    x <> y.
Proof.
  induction l; intros; simpl; auto.
  destruct H.
  - routine.
  - apply IHl; trivial.
    tidy_up. intuition.
Qed.

Lemma binds_for_sure : forall A (l1 l2 : list (var * A)) x a,
    binds x a (l1 ++ x ~ a ++ l2).
Proof.
  induction on list; routine.
  right. apply IHlist.
Qed.

Lemma Forall_app1 : forall A (l1 l2 : list A) P,
    Forall P (l1 ++ l2) ->
    Forall P l1.
Proof. induction on list; eroutine. Qed.

Lemma Forall_app2 : forall A (l1 l2 : list A) P,
    Forall P (l1 ++ l2) ->
    Forall P l2.
Proof. induction on list; eroutine. Qed.

Lemma split_at_None : forall A x (l : list (var * A)),
    split_at x l = None ->
    x `notin` dom l.
Proof.
  induction on list; intros.
  - routine.
  - simpl in *. tidy_up.
    destruct (H0 == a) eqn:?; tidy_up.
    destruct (split_at H0 H1) eqn:?; tidy_up.
    specialize (IHlist eq_refl).
    solve_notin.
Qed.

Lemma uniq_witness : forall A (l1 l2 l3 l4 : list (var * A)) x a b,
    l1 ++ x ~ a ++ l2 = l3 ++ x ~ b ++ l4 ->
    uniq (l1 ++ x ~ a ++ l2) ->
    l1 = l3 /\ a = b /\ l2 = l4.
Proof.
  induction on list; simpl; intros.
  - destruct l3; simpl; [routine |].
    destruct p; tidy_up.
    exfalso. apply H6. set simpl.
    fsetdec.
  - destruct a, l3; simpl in *; tidy_up.
    + exfalso. apply H7. set simpl. 
      fsetdec.
    + apply IHlist in H8; trivial. tidy_up.
      auto.
Qed.

Lemma split_at_uniq : forall A (l1 l2 : list (var * A)) x a,
    uniq (l1 ++ x ~ a ++ l2) ->
    exists pf, split_at x (l1 ++ x ~ a ++ l2) =
          Some (existT _ a (existT _ l2 (exist _ l1 pf))).
Proof.
  induction l1; intros; simpl.
  - destruct (x == x); try congruence.
    eexists. reflexivity.
  - tidy_up. assert (x <> a) by auto.
    destruct (x == a); try congruence.
    destruct (split_at x (l1 ++ (x, a0) :: l2)) eqn:?.
    + tidy_up. pose proof H1.
      apply uniq_witness in H3; trivial. tidy_up.
      eexists. reflexivity.
    + exfalso. apply split_at_None in Heqo.
      apply Heqo. set simpl. fsetdec.
Qed.

Lemma split_at_Some : forall A (l : list (var * A)) x r,
    split_at x l = Some r ->
    x `in` dom l.
Proof.
  induction l; intros; simpl in *.
  - congruence.
  - tidy_up. destruct (x == a); subst; auto.
    destruct (split_at x l).
    + tidy_up. set simpl. fsetdec.
    + congruence.
Qed.

Section PairWf.

  Context (A B : Type).
  Variable (f : A -> nat) (g : B -> nat).

  Definition leA (a1 a2 : A) :=
    f a1 < f a2.

  Definition leB (b1 b2 : B) :=
    g b1 < g b2.

  Definition lprod := lexprod _ _ leA (fun _ => leB).
  
  Lemma lprod_wf : well_founded lprod.
  Proof.
    apply wf_lexprod.
    - apply well_founded_ltof.
    - intros. apply well_founded_ltof.
  Defined.
  
  Definition sprod := symprod A B leA leB.
  
  Lemma sprod_wf : well_founded sprod.
  Proof.
    apply wf_symprod; apply well_founded_ltof.
  Defined.

End PairWf.
Arguments leA {A} f a1 a2/.
Arguments leB {B} g b1 b2/.

Lemma prefix_uniq : forall A (l l' : list (var * A)),
    prefix l l' ->
    uniq l' ->
    uniq l.
Proof. induction on @prefix; routine. Qed.

Lemma in_to_binds: forall A x l,
    x `in` dom l ->
    exists a : A, binds x a l.
Proof.
  induction l; intros; simpl in *.
  - fsetdec.
  - tidy_up. apply add_iff in H.
    tidy_up; eauto.
    apply IHl in H. tidy_up; eauto.
Qed.

Lemma binds_app : forall A x (a : A) l,
    binds x a l ->
    exists l1 l2, l = l1 ++ x ~ a ++ l2.
Proof.
  induction l; routine.
  - exists nil, l. trivial.
  - apply IHl in H. tidy_up.
    do 2 eexists. reassoc 4 with 2.
    reflexivity.
Qed.

Lemma in_prefix_binds : forall A l l1 l2 x (T : A),
    x `in` dom l ->
    prefix l (l1 ++ x ~ T ++ l2) ->
    uniq (l1 ++ x ~ T ++ l2) ->
    exists l', l = l' ++ x ~ T ++ l2 /\ prefix l' l1.
Proof.
  intros. apply in_to_binds in H.
  tidy_up.
  pose proof (prefix_uniq H0 ltac:(trivial)).
  apply binds_app in H2. 
  rewrite prefix_iff_app in H0.
  tidy_up.
  replace (H0 ++ H2 ++ (x, H) :: H5) with ((H0 ++ H2) ++ x ~ H ++ H5) in H4.
  apply uniq_witness in H4; trivial; tidy_up.
  - eexists; split; trivial.
    apply prefix_app.
  - rewrite app_assoc. trivial.
Qed.
