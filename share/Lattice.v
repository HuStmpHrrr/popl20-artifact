(** Different formulation of bounded lattices, (L, 0, 1, ∨, ∧).
  * 
  * we can form algebraic lattices or order theoretic lattices.
  * 
  * not sure which one is better. we can try both.
  *)

Require Import Coq.Classes.RelationClasses.
Require Import Coq.Setoids.Setoid.
Require Import Coq.Program.Tactics.

Section InducedEquivalence.

  Context {A : Type} (relA : relation A).

  Definition equiv (x y : A) : Prop := relA x y /\ relA y x.
  Hint Unfold equiv.
  Hint Transparent equiv.
  
  Global Instance InducedEquivalence `(PreOrder A relA) : Equivalence equiv := {}.
  Proof.
    all:autounfold; intros.
    - split; apply reflexivity.
    - tauto.
    - destruct_pairs. split; eapply transitivity; eassumption.
  Qed.

End InducedEquivalence.
Hint Unfold equiv.
Hint Transparent equiv.
  
Module Algebraic.

  (** Algebraic lattice *)
  Class ALattice {C : Type} (eq : C -> C -> Prop) `(equiv: Equivalence C eq) :=
    {
      top : C;
      bot : C;
      sup : C -> C -> C;
      inf : C -> C -> C;

      (** laws *)
      top_bound : forall x, eq (inf x top) x;
      bot_bound : forall x, eq (sup x bot) x;
      
      sup_comm : forall x y, eq (sup x y) (sup y x);
      inf_comm : forall x y, eq (inf x y) (inf y x);

      sup_assoc : forall x y z, eq (sup x (sup y z)) (sup (sup x y) z);
      inf_assoc : forall x y z, eq (inf x (inf y z)) (inf (inf x y) z);

      sup_absorb : forall x y, eq (sup x (inf x y)) x;
      inf_absorb : forall x y, eq (inf x (sup x y)) x
    }.

End Algebraic.

Module Order.
  
  (** A order theoretic lattice *)
  Class OLattice {C : Type} (pord : C -> C -> Prop) `(po : PreOrder C pord) :=
    {
      top : C;
      bot : C;
      sup : C -> C -> C;
      inf : C -> C -> C;

      (** laws *)
      top_bound : forall x, pord x top;
      bot_bound : forall x, pord bot x;

      sup_I1 : forall x y, pord x (sup x y);
      sup_I2 : forall x y, pord y (sup x y);
      sup_E : forall x y z, pord x z -> pord y z -> pord (sup x y) z;

      inf_E1 : forall x y, pord (inf x y) x;
      inf_E2 : forall x y, pord (inf x y) y;
      inf_I : forall w x y, pord w x -> pord w y -> pord w (inf x y)
    }.

End Order.

Section OLatticeImpliesALattice.
  Import Order.

  Context {C : Type} (pord : C -> C -> Prop).
  Context `{po : PreOrder C pord} `{ol : @OLattice C pord po}.

  (** It's derivable that order theoretic lattice implies algebraic lattice. *)
  Global Instance OLattice_ALattice : Algebraic.ALattice (equiv pord) (InducedEquivalence _ po)
    := {
        top := top;
        bot := bot;
        sup := sup;
        inf := inf
      }.
  Proof.
    all:autounfold; intros.
    - split.
      + apply inf_E1.
      + apply inf_I; [apply reflexivity | apply top_bound].

    - split.
      + apply sup_E; [apply reflexivity | apply bot_bound].
      + apply sup_I1.

    - split.
      + apply sup_E; [apply sup_I2 | apply sup_I1].
      + apply sup_E; [apply sup_I2 | apply sup_I1].

    - split.
      + apply inf_I; [apply inf_E2 | apply inf_E1].
      + apply inf_I; [apply inf_E2 | apply inf_E1].

    - split.
      + repeat apply sup_E.
        * eapply transitivity. apply sup_I1. apply sup_I1.
        * eapply transitivity. apply sup_I2. apply sup_I1.
        * apply sup_I2.
      + repeat apply sup_E.
        * apply sup_I1.
        * eapply transitivity. apply sup_I1. apply sup_I2.
        * eapply transitivity. apply sup_I2. apply sup_I2.

    - split.
      + repeat apply inf_I.
        * apply inf_E1.
        * eapply transitivity. apply inf_E2. apply inf_E1.
        * eapply transitivity. apply inf_E2. apply inf_E2.
      + repeat apply inf_I.
        * eapply transitivity. apply inf_E1. apply inf_E1.
        * eapply transitivity. apply inf_E1. apply inf_E2.
        * apply inf_E2.

    - split.
      + apply sup_E; [apply reflexivity | apply inf_E1].
      + apply sup_I1.

    - split.
      + apply inf_E1.
      + apply inf_I; [apply reflexivity | apply sup_I1].
  Qed.

End OLatticeImpliesALattice.