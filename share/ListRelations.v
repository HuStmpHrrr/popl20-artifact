Set Implicit Arguments.
Require Import LibUtils.
Require Import Coq.Lists.List.
Import ListNotations.
Require Import Metalib.Metatheory.
Require Import Lia.
Require Import MetaExt.

Notation included l1 l2 := (Forall (fun x => In x l2) l1).
Local Hint Constructors Forall.
Local Hint Resolve in_or_app.

Section Included.

  Context {A : Type}.

  Local Ltac init :=
    intros; repeat rewrite Forall_forall in *; intros.

  Local Ltac spec :=
    lazymatch goal with
    | H : forall x, In x _ -> _, H' : In _ _ |- _ =>
      specialize (H _ H')
    end.

  Local Ltac dang := init; spec; auto.
  
  Lemma included_cons : forall (l1 l2 : list A) x,
      included l1 l2 ->
      included l1 (x :: l2).
  Proof. dang. right; auto. Qed.

  Lemma included_app1 : forall (l1 l2 l3 : list A),
      included l1 l2 ->
      included l1 (l2 ++ l3).
  Proof. dang. Qed.

  Lemma included_app2 : forall (l1 l2 l3 : list A),
      included l1 l3 ->
      included l1 (l2 ++ l3).
  Proof. dang. Qed.

  Lemma included_app3 : forall (l1 l2 l3 : list A),
      included (l1 ++ l2) l3 ->
      included l1 l3 /\ included l2 l3.
  Proof.
    init. split; intros; apply H.
    all:rewrite in_app_iff; auto.
  Qed.
    
End Included.       
             
Section OrderPreservingEmbeddings.

  Context {A : Type}.

  (** l1 <= l2 *)
  Inductive ope_list : list A -> list A -> Prop :=
  | ol_nil : ope_list nil nil
  | ol_keep : forall x l1 l2, ope_list l1 l2 -> ope_list (x :: l1) (x :: l2)
  | ol_drop : forall x l1 l2, ope_list l1 l2 -> ope_list l1 (x :: l2).
  Hint Constructors ope_list.

  Local Ltac ind_list l :=
    induction l; intros; simpl in *; auto.
  
  Lemma ope_list_refl : forall l,
      ope_list l l.
  Proof. ind_list l. Qed.
  Local Hint Resolve ope_list_refl.

  Lemma ope_list_to_nil : forall l,
      ope_list [ ] l.
  Proof. ind_list l. Qed.
  Local Hint Resolve ope_list_to_nil.

  Lemma ope_list_trans : forall l1 l2 l3,
      ope_list l1 l2 ->
      ope_list l2 l3 ->
      ope_list l1 l3.
  Proof.
    intros. generalize dependent l1.
    induction H0; intros; auto.
    inversion H; subst; auto.
  Qed.

  Lemma ope_list_append1 : forall l1 l2,
      ope_list l1 (l1 ++ l2).
  Proof. ind_list l1. Qed.

  Lemma ope_list_append2 : forall l1 l2,
      ope_list l2 (l1 ++ l2).
  Proof. ind_list l1. Qed.

  Lemma ope_list_implies_included : forall l1 l2,
      ope_list l1 l2 ->
      included l1 l2.
  Proof.
    induction 1; auto.
    all: rewrite Forall_forall in *; intros.
    - destruct H0; subst;
        [left | right]; auto.
    - right; auto.
  Qed.

  Lemma ope_list_length : forall l1 l2,
      ope_list l1 l2 ->
      length l1 <= length l2.
  Proof. induction 1; simpl; lia. Qed.

  Lemma ope_list_decons : forall x l1 l2,
      ope_list (x :: l1) l2 ->
      ope_list l1 l2.
  Proof.
    intros. remember (x :: l1).
    revert Heql. revert l1.
    induction H; intros; try congruence.
    - inversion Heql; subst. auto.
    - subst. constructor.
      apply IHope_list. trivial.
  Qed.
  Local Hint Resolve ope_list_decons.
  
  Lemma ope_list_inv : forall x l1 l2,
      ope_list (x :: l1) (x :: l2) ->
      ope_list l1 l2.
  Proof.
    intros. remember (x :: l1). remember (x :: l2).
    revert Heql Heql0. revert l1 l2.
    induction H; intros; try congruence.
    inversion Heql0; subst.
    eauto.
  Qed.
  Local Hint Resolve ope_list_inv.
  
  Lemma ope_list_antisym : forall l1 l2,
      ope_list l1 l2 ->
      ope_list l2 l1 ->
      l1 = l2.
  Proof.
    induction 1; intros; trivial.
    - f_equal; auto. apply IHope_list.
      eauto.
    - apply ope_list_length in H.
      apply ope_list_length in H0.
      simpl in H0. lia.
  Qed.

  Global Instance PreorderOpe : PreOrder ope_list :=
    {
      PreOrder_Reflexive := ope_list_refl;
      PreOrder_Transitive := ope_list_trans
    }.

  Global Instance PartialOrderOpe : @PartialOrder _ _ eq_equivalence _ PreorderOpe :=
    { }.
  Proof.
    repeat split; subst; cbv; auto.
    intros. destruct H.
    apply ope_list_antisym; assumption.
  Qed.
  
End OrderPreservingEmbeddings.

Section DecMembership.

  Context {A : Type} {eqA : EqDec_eq A}.
  
  Definition In_dec (a : A) (l : list A)
    : { In a l } + { ~ In a l }.
  Proof. apply in_dec. apply eqA. Defined.
  
  Definition In_remove (a : A) (l : list A) : list A.
  Proof. exact (List.remove eqA a l). Defined.

  Theorem In_removed : forall a l, ~In a (In_remove a l).
  Proof.
    unfold In_remove. intros.
    apply remove_In.
  Qed.

  Theorem remove_length_invar : forall (a : A) l,
      length (In_remove a l) <= length l.
  Proof.
    induction l; simpl; intros; auto.
    destruct (eqA a a0); subst; simpl; lia.
  Qed.
  
  Theorem remove_length : forall (a : A) l,
      In a l ->
      length (In_remove a l) < length l.
  Proof.
    induction l; simpl; intros.
    - intuition.
    - destruct (eqA a a0); subst.
      + pose proof (remove_length_invar a0 l).
        lia.
      + destruct H; try congruence.
        specialize (IHl H).
        simpl. lia.
  Qed.


  Lemma in_before_removal : forall a l b,
      In b (In_remove a l) ->
      In b l.
  Proof.
    induction l; simpl; intros; auto.
    destruct (eqA a a0).
    - subst. auto.
    - destruct H; auto.
  Qed.

  Lemma eq_after_removal : forall a l b,
      In b l ->
      ~In b (In_remove a l) ->
      a = b.
  Proof.
    induction l; simpl; intros; auto.
    - contradiction.
    - destruct (eqA a a0).
      + subst. destruct H; auto.
      + destruct H.
        * subst. exfalso. apply H0. left. trivial.
        * apply IHl; trivial.
          intro Contra; apply H0. right. auto.
  Qed.
  
  Hint Resolve ope_list_refl.
  Hint Constructors ope_list.
  
  Lemma In_remove_ope_list : forall (x : A) l,
      ope_list (In_remove x l) l.
  Proof.
    induction l; intros; simpl; auto.
    destruct (eqA x a); simpl; auto.
  Qed.

  Lemma not_ope_after_removal : forall (x : A) l,
      In x l ->
      ~ope_list l (In_remove x l).
  Proof.
    intros. intro Contra.
    apply ope_list_length in Contra.
    apply remove_length in H.
    lia.
  Qed.
  
End DecMembership.

Section AtomLists.

  Theorem remove_from_list : forall a l S S',
    Forall (fun v => v `notin` S) (In_remove a l) ->
    S' [<=] S ->
    a `notin` S' ->
    Forall (fun v => v `notin` S') l.
  Proof.
    induction l; intros; auto.
    simpl in H.
    change (EqDec_eq_of_X a a0) with (a == a0) in H.
    constructor.
    - simpl in H. 
      destruct (a == a0); subst; trivial.
      inversion H; subst. 
      set solve.
    - eapply IHl; auto.
      destruct (a == a0); subst; auto.
  Qed.

End AtomLists.

(* l1 is a prefix of l2 *)
Inductive prefix {A} : list A -> list A -> Prop :=
| pf_refl : forall l, prefix l l
| pf_cons : forall a l1 l2, prefix l1 l2 -> prefix l1 (a :: l2).
Local Hint Constructors prefix.

Section PrefixProperties.

  Context {A : Type}.
  Implicit Type a : A.
  Implicit Type l : list A.
  
  Lemma prefix_to_app : forall l1 l2,
      prefix l1 l2 ->
      exists l, l2 = l ++ l1.
  Proof.
    induction on @prefix.
    - exists nil. easy.
    - tidy_up. eexists.
      instantiate (1 := ltac:(apply cons)).
      simpl. reflexivity.
  Qed.

  Lemma app_to_prefix : forall l1 l2 l3,
      l1 ++ l2 = l3 ->
      prefix l2 l3.
  Proof. induction l1; routine. Qed.

  Lemma prefix_iff_app : forall l1 l2,
      prefix l1 l2 <-> exists l, l2 = l ++ l1.
  Proof.
    split.
    - apply prefix_to_app.
    - intros. tidy_up.
      eapply app_to_prefix.
      eauto.
  Qed.
  
  Lemma prefix_nil : forall l,
      prefix nil l.
  Proof. induction on list; routine. Qed.

  Lemma prefix_app : forall l' l,
      prefix l (l' ++ l).
  Proof. induction l'; routine. Qed.
  Hint Resolve prefix_app.
  
  Lemma prefix_deapp : forall l1 l2 l3,
      prefix (l1 ++ l2) l3 ->
      prefix l2 l3.
  Proof. dep induction on @prefix; eauto. Qed.

  Lemma prefix_decons : forall a l1 l2,
      prefix (a :: l1) l2 ->
      prefix l1 l2.
  Proof.
    intros. eapply prefix_deapp.
    instantiate (1 := cons a nil).
    trivial.
  Qed.
  Hint Resolve prefix_decons.

  Lemma prefix_dom : forall A (l1 l2 : list (var * A)),
      prefix l1 l2 ->
      dom l1 [<=] dom l2.
  Proof.
    induction on @prefix; routine.
  Qed.
  
  Lemma prefix_trans : forall l1 l2 l3,
      prefix l1 l2 ->
      prefix l2 l3 ->
      prefix l1 l3.
  Proof.
    intros. gen l3.
    induction H; eroutine.
  Qed.

  Global Instance PrefixPreOrder : PreOrder (@prefix A) := { }.
  Proof.
    - exact pf_refl.
    - exact prefix_trans.
  Qed.
  
End PrefixProperties.

Section OpeListProperties.
  Hint Constructors ope_list.
  Hint Resolve ope_list_refl ope_list_trans ope_list_to_nil.
  
  Context {A : Type}.
  Implicit Type x : var.
  Implicit Type a : A.
  Implicit Type l : list (var * A).

  Lemma prefix_is_ope_list : forall l1 l2,
      prefix l1 l2 ->
      ope_list l1 l2.
  Proof. induction on @prefix; routine. Qed.
  
  Lemma ope_list_dom : forall l1 l2,
      ope_list l1 l2 ->
      dom l1 [<=] dom l2.
  Proof.
    induction on @ope_list; set solve.
    destruct_conjs. simpl.
    set solve.
  Qed.
  
  Lemma ope_list_uniq : forall l1 l2,
      ope_list l1 l2 ->
      uniq l2 ->
      uniq l1.
  Proof.
    induction on @ope_list; routine.
    constructor; auto.
    pose proof (ope_list_dom H1).
    set solve.
  Qed.

  Lemma ope_list_witness_uniq_gen :
    forall l l',
      ope_list l l' ->
    forall x a1 a2 l1 l2 l3 l4,
      l = l1 ++ x ~ a1 ++ l2 ->
      l' = l3 ++ x ~ a2 ++ l4 ->                               
      uniq l' ->
      ope_list l1 l3 /\ a1 = a2 /\ ope_list l2 l4.
   Proof.
     induction on @ope_list; intros; destruct_conjs.
     - apply List.app_cons_not_nil in H.
       contradiction.
     - destruct l0, l4; simpl in *; progressive_inversions.
       + repeat split; trivial.
       + exfalso. solve_uniq.
       + exfalso. pose proof (ope_list_dom H1).
         set simpl in *. destruct_conjs. set solve.
       + edestruct IHope_list; try reflexivity; trivial.
         destruct_conjs.
         repeat split; auto.
     - subst l1.
       destruct l4; simpl in *; progressive_inversions.
       + exfalso. pose proof (ope_list_dom H1).
         set simpl in *. destruct_conjs; set solve.
       + edestruct IHope_list; try reflexivity; trivial.
         destruct_conjs.
         auto.
   Qed.
  
  Lemma ope_list_witness_uniq : forall {x a1 a2 l1 l2 l3 l4},
      ope_list (l1 ++ x ~ a1 ++ l2) (l3 ++ x ~ a2 ++ l4) ->
      uniq (l3 ++ x ~ a2 ++ l4) ->
      ope_list l1 l3 /\ a1 = a2 /\ ope_list l2 l4.
  Proof.
    intros. eapply ope_list_witness_uniq_gen; eauto.
  Qed.

End OpeListProperties.
