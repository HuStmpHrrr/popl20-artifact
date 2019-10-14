(* set up monads. *)
Require Export ExtLib.Structures.Monad.
Require Export ExtLib.Structures.MonadExc.
Export MonadNotation.
Open Scope monad.
Require Export ExtLib.Data.Monads.OptionMonad.
Require Export ExtLib.Data.Monads.EitherMonad.
Require Import String.

Inductive Err : Type :=
| err : forall {E}, E -> Err
| err_cons : forall {E}, Err -> E -> Err.

Inductive Result (A : Type) : Type :=
| res_ret : A -> Result A
| err_ret : Err -> Result A.

Instance ResultMonad : Monad Result := {}.
Proof.
  - (* ret *) intros A x. exact (res_ret A x).
  - (* bind *) intros A B retA bmap.
    destruct retA.
    + destruct (bmap a).
      * exact (res_ret B b).
      * exact (err_ret _ (err_cons e a)).
    + exact (err_ret _ e).
Defined.

Definition eret {A : Type} {E : Type} (e : E) : Result A :=
  err_ret _ (err e).

(** Now we have a new monad *)

Notation Tc A := (sum (list string) A).
Definition err_msg {A} (m : Tc A) (msg : string) :=
  match m with
  | inl msgs => inl (cons msg msgs)
  | inr x => inr x
  end.

Notation "m !!> s" := (err_msg m s) (at level 95).
Definition erret {A} (m : string) : Tc A :=
  inl (cons m nil).
Arguments erret {A} m/.

Definition option_to_Tc {A} (o : option A) (m : String.string) : Tc A :=
  match o with
  | Some r => ret r
  | None => erret m
  end.

Create HintDb monads discriminated.

Tactic Notation "monads" "simpl" := autorewrite with monads.
Tactic Notation "monads" "simpl" "in" "*" := autorewrite with monads in *.

Lemma option_to_Tc_preserves_result1 : forall A (o : option A) s r,
    option_to_Tc o s = inr r <->
    o = Some r.
Proof.
  destruct o; split; cbv in *; intros; congruence.
Qed.

Lemma option_to_Tc_preserves_result2 : forall A (o : option A) s l,
    option_to_Tc o s = inl l ->
    o = None.
Proof.
  destruct o; cbv in *; intros; congruence.
Qed.

Hint Rewrite -> option_to_Tc_preserves_result1 : monads.
Hint Resolve option_to_Tc_preserves_result2 : monads.

Lemma err_msg_preserves_result : forall A (o : Tc A) s r,
    (o !!> s) = inr r <->
    o = inr r.
Proof.
  destruct o; split; cbv in *; intros; congruence.
Qed.
Hint Rewrite -> err_msg_preserves_result : monads.

(** we use this type to swallow unexpected cases.
 * we must discharge this case somewhere after it's used temporarily.
 *)
Inductive error : Set := err_case : error.

Ltac reveal_err :=
  repeat lazymatch goal with
         | e : error |- _ => destruct e
         end.

Definition TcE A : Type := (error + Tc A).

Definition err_out {A} : TcE A := inl err_case.
Arguments err_out {A}/.

Definition err_msge {A} (m : TcE A) (msg : string) : TcE A :=
  match m with
  | inl e => inl e
  | inr (inl msgs) => inr (inl (cons msg msgs))
  | inr (inr x) => inr (inr x)
  end.

Notation "m !!!> s" := (err_msge m s) (at level 95).
Definition errete {A} (m : string) : TcE A :=
  inr (inl (cons m nil)).
Arguments errete {A} m/.

Definition option_to_TcE {A} (o : option A) : TcE A :=
  match o with
  | Some r => inr (inr r)
  | None => err_out
  end.

Instance TcEMonad : Monad TcE | 0 := { }.
Proof.
  - intros. exact (inr (inr X)).
  - intros.
    refine (match X with
            | inl e => inl e
            | inr (inl msgs) => inr (inl msgs)
            | inr (inr t) => X0 t
            end).
Defined.

Lemma option_to_TcE_preserves_result1 : forall A (o : option A) r,
    option_to_TcE o = inr (inr r) <->
    o = Some r.
Proof.
  destruct o; split; cbv in *; intros; congruence.
Qed.
Hint Rewrite -> option_to_TcE_preserves_result1 : monads.

Lemma option_to_TcE_preserves_result2 : forall A (o : option A),
    option_to_TcE o = inl err_case <->
    o = None.
Proof.
  destruct o; split; cbv in *; intros; congruence.
Qed.
Hint Rewrite -> option_to_TcE_preserves_result2 : monads.

Lemma err_msge_preserves_result1 : forall A (o : TcE A) s r,
    (o !!!> s) = inr (inr r) <->
    o = inr (inr r).
Proof.
  destruct o; split; cbv in *; intros; try congruence.
  - destruct s; congruence.
  - destruct s; congruence.
Qed.
Hint Rewrite -> err_msge_preserves_result1 : monads.

Lemma err_msge_preserves_result2 : forall A (o : TcE A) s,
    (o !!!> s) = inl err_case <->
    o = inl err_case.
Proof.
  destruct o; split; cbv in *; intros; try congruence.
  destruct s; congruence.
Qed.
Hint Rewrite -> err_msge_preserves_result2 : monads.

Existing Instance Monad_either | 1.