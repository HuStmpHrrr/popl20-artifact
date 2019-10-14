Require Import Metalib.Metatheory.


Class CanOpen (A : Type) :=
  {
    open_rec (k : nat) (u : var) (ins : A) : A
  }.

Notation open := (open_rec 0).

Ltac fold_open_rec :=
  let pred f :=
      lazymatch f with
      | context[open_rec] => fail
      | _ => idtac
      end in
  repeat match goal with
         | [ H : context[?f ?x ?y ?t] |- _ ] =>
           pred f; change (f x y t) with (open_rec x y t) in H
         | |- context[?f ?x ?y ?t] =>
           pred f; change (f x y t) with (open_rec x y t)
         end.

Class CanClose (A : Type) :=
  {
    close_rec (k : nat) (u : var) (ins : A) : A
  }.

Notation close := (close_rec 0).

Ltac fold_close_rec :=
  let pred f :=
      lazymatch f with
      | context[close_rec] => fail
      | _ => idtac
      end in
  repeat match goal with
         | [ H : context[?f ?x ?y ?t] |- _ ] =>
           pred f; change (f x y t) with (close_rec x y t) in H
         | |- context[?f ?x ?y ?t] =>
           pred f; change (f x y t) with (close_rec x y t)
         end.


Class HasFv (A : Type) :=
  {
    fv (ins : A) : atoms
  }.

Ltac fold_fv :=
  let pred f :=
      lazymatch f with
      | context[fv] => fail
      | _ => idtac
      end in
  repeat match goal with
         | [ H : context[?f ?x] |- _ ] =>
           pred f; change (f x) with (fv x) in H
         | |- context[?f ?x] =>
           pred f; change (f x) with (fv x)
         end.

Class CanSubst (A : Type) :=
  {
    substi (z u : var) (ins : A) : A
  }.

Ltac fold_substi :=
  let pred f :=
      lazymatch f with
      | context[substi] => fail
      | _ => idtac
      end in
  repeat match goal with
         | [ H : context[?f ?x ?y ?t] |- _ ] =>
           pred f; change (f x y t) with (substi x y t) in H
         | |- context[?f ?x ?y ?t] =>
           pred f; change (f x y t) with (substi x y t)
         end.

Class LC (A : Type) :=
  {
    lc_at (n : nat) (ins : A) : Prop
  }.
Notation lc := (lc_at 0).

Ltac fold_lc_at :=
  let pred f :=
      lazymatch f with
      | context[lc_at] => fail
      | _ => idtac
      end in
  repeat match goal with
         | [ H : context[?f ?x ?y] |- _ ] =>
           pred f; change (f x y) with (lc_at x y) in H
         | |- context[?f ?x ?y] =>
           pred f; change (f x y) with (lc_at x y)
         end.

Ltac fold_cls :=
  fold_open_rec; fold_close_rec; fold_fv;
  fold_substi; fold_lc_at.
