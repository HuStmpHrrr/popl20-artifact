Require Import StdSetup.

(** * Definition of Variables *)

(** Variables are represented locally namelessly with cofinite quantification.  That
    is, local names are represented by de Bruijn indices, while names in the contexts
    are represented by free names. 
 *)

Inductive avar : Set :=
| avar_b : nat -> avar
| avar_f : var -> avar.
Hint Constructors avar.

Instance EqAvar : EqDec_eq avar := { }.
Proof. decide equality. apply Nat.eq_dec. Defined.

Definition fv_values {T : Type} (f : T -> atoms)
           (l : list (atom * T)) : atoms :=
  fold_right (fun (b : (atom * T)) a =>
                a \u let (_, t) := b in f t) {} l.

Lemma fv_unpack : forall T (f : T -> _) e1 e2,
    fv_values f (e1 ++ e2) [=] fv_values f e1 `union` fv_values f e2.
Proof.
  induction on list; intros. simpl.
  - set solve.
  - routine.
    + rewrite IHlist in H2. fsetdec.
    + rewrite IHlist. fsetdec.
Qed.

Hint Rewrite -> dom_app fv_unpack : meta_ext.
