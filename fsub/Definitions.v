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

Require Export StdSetup.

(** * Abstract Syntax *)

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


(** ** Types
    - [typ_top] represents the [⊤] type.
    - [typ_var x] represents a type variable [X].
    - [typ_fun S U] represents a function type (S ⟶ U)
    - [typ_all S U] represents a universal type [∀ X <: S . U].
 *)
Inductive typ : Set :=
| typ_top : typ
| typ_var : avar -> typ
| typ_fun : typ -> typ -> typ (* trm functions *)
| typ_all : typ -> typ -> typ. (* typ functions \ universal types *)
Hint Constructors typ.

(** * Basic Characteristics

    Here we define some basic characteristics of the abstract syntax, including local
 closure, the opening, closing and substitution operations, and the retrieval of free
 variables of variables, types, terms and values.

 This library uses a number of type classes to capture these characteristics,
 including [LC], [CanOpen], [CanClose] and [HasFv]. Thus, each characteristic can be
 represented by one single predicate.  *)
Inductive lc_avar_at : nat -> avar -> Prop :=
| lc_ab : forall {n m}, n < m -> lc_avar_at m (avar_b n)
| lc_af : forall {n x}, lc_avar_at n (avar_f x).

Instance LcTvar : LC avar := { lc_at := lc_avar_at }.

Inductive lc_typ_at : nat -> typ -> Prop :=
| lc_typ_top : forall {n}, lc_typ_at n typ_top
| lc_typ_var : forall {n X}, lc_at n X -> lc_typ_at n (typ_var X)

| lc_typ_fun : forall {n T U}, lc_typ_at n T -> lc_typ_at n U ->
                          lc_typ_at n (typ_fun T U)
| lc_typ_all : forall {n T U}, lc_typ_at n T -> lc_typ_at (S n) U ->
                           lc_typ_at n (typ_all T U).

Instance LcFtyp : LC typ := { lc_at := lc_typ_at }.
Hint Constructors lc_avar_at lc_typ_at.

Definition open_rec_tvar (k : nat) (u : var) (a : avar) : avar :=
  match a with
  | avar_b i => if k == i then avar_f u else avar_b i
  | avar_f x => avar_f x
  end.

Fixpoint open_rec_typ (k : nat) (u : var) (T : typ) : typ :=
  match T with
  | typ_top => typ_top
  | typ_var X => typ_var (open_rec_tvar k u X)
  | typ_fun T U => typ_fun (open_rec_typ k u T) (open_rec_typ k u U)
  | typ_all T U => typ_all (open_rec_typ k u T) $ open_rec_typ (S k) u U
  end.

Instance OpenTvar : CanOpen avar := { open_rec := open_rec_tvar }.
Instance OpenTyp : CanOpen typ := { open_rec := open_rec_typ }.

Definition close_rec_tvar (k : nat) (u : var) (a : avar) : avar :=
    match a with
    | avar_b n => avar_b n
    | avar_f x => if x == u then avar_b k else avar_f x
    end.

Fixpoint close_rec_typ (k : nat) (u : var) (T : typ) : typ :=
  match T with
  | typ_top => typ_top
  | typ_var X => typ_var (close_rec_tvar k u X)
  | typ_fun T U => typ_fun (close_rec_typ k u T) (close_rec_typ k u U)
  | typ_all T U => typ_all (close_rec_typ k u T) $ close_rec_typ (S k) u U
  end.

Instance CloseTvar : CanClose avar := { close_rec := close_rec_tvar }.
Instance CloseTyp : CanClose typ := { close_rec := close_rec_typ }.

Definition subst_tvar (z u: var) (a : avar) : avar :=
  match a with
  | avar_b i as a => a
  | avar_f x => avar_f $ if x == z then u else x
  end.

Fixpoint subst_typ (z u: var) (T : typ) : typ := 
  match T with
  | typ_top => typ_top
  | typ_var X => typ_var (subst_tvar z u X)
  | typ_fun T U => typ_fun (subst_typ z u T) (subst_typ z u U)
  | typ_all T U => typ_all (subst_typ z u T) $ subst_typ z u  U
  end.

Instance SubstTvar : CanSubst avar := { substi := subst_tvar }.
Instance SubstTyp : CanSubst typ := { substi := subst_typ }.

Notation env := (list (var * typ)).

Definition fv_avar (v : avar) : vars :=
  match v with
  | avar_b _ => {}
  | avar_f x => {{ x }}
  end.
  
Fixpoint fv_typ (T : typ) : vars :=
  match T with
  | typ_top => empty
  | typ_var X => fv_avar X
  | typ_fun T U => fv_typ T \u fv_typ U
  | typ_all T U => fv_typ T \u fv_typ U
  end.

Instance FvTvar : HasFv avar := { fv := fv_avar }.
Instance FvTyp : HasFv typ := { fv := fv_typ }.
Instance FvEnv : HasFv env := { fv := fun e => dom e `union` fv_values fv e }.

Lemma fv_union : forall (e1 e2 : env) , fv (e1 ++ e2) [=] fv e1 `union` fv e2.
Proof.
  intros; simpl. 
  apply AtomSetProperties.subset_antisym;
    set solve.
Qed.

Hint Rewrite -> fv_union : meta_ext.

Ltac gather_atoms ::=
  let A := gather_atoms_with (fun x : atoms => x) in
  let B := gather_atoms_with (fun x : atom => singleton x) in
  let C := gather_atoms_with (fun x : env => fv x) in
  let D := gather_atoms_with fv_avar in
  let E := gather_atoms_with fv_typ in
  constr:(A `union` B `union` C `union` D `union` E).

Reserved Notation "G ⊢F S <⦂ U" (at level 90).
Inductive subty : env -> typ -> typ -> Prop :=
(** [――――――――――] F-Top #<br>#
    [G ⊢ T <: ⊤]  *)
| st_top : forall (G : env) (T : typ),
    G ⊢F T <⦂ typ_top
(** [――――――――――] F-VarRefl #<br>#
    [G ⊢ X <: X]  *)
| st_vrefl : forall (G : env) (X : avar),
    G ⊢F typ_var X <⦂ typ_var X
(** [X <: T ∈ G] #<br>#
    [G ⊢ T <: U] #<br>#
    [――――――――――] F-Tvar' #<br>#
    [G ⊢ X <: U]  *)
| st_bind : forall (G : env) (x : atom) (T U : typ),
    binds x T G ->
    G ⊢F T <⦂ U ->
    G ⊢F typ_var (avar_f x) <⦂ U
(** [G ⊢ T1 <: S1] #<br>#
    [G ⊢ S2 <: T2] #<br>#
    [――――――――――――――――――――――] F-Fun #<br>#
    [G ⊢ S1 ⟶ S2 <: T1 ⟶ T2]  *)
| st_fun : forall (G : env) (S1 S2 T1 T2 : typ),
    G ⊢F T1 <⦂ S1 ->
    G ⊢F S2 <⦂ T2 ->
    G ⊢F typ_fun S1 S2 <⦂ typ_fun T1 T2
(** [G ⊢ T1 <: S1] #<br>#
    [G ; X <: T1 ⊢ S2 <: T2] #<br>#
    [―――――――――――――――――――――――――――――――――――――] F-All #<br>#
    [G ⊢ (∀ X<: S1. S2) <: (∀ X <: T1. T2)]  *)
| st_all : forall (L : atoms) (G : env) (S1 S2 T1 T2 : typ),
    G ⊢F T1 <⦂ S1 ->
    (forall x : atom, x `notin` L -> [(x, T1)] ++ G ⊢F open x S2 <⦂ open x T2) ->
    G ⊢F typ_all S1 S2 <⦂ typ_all T1 T2
where "G ⊢F S <⦂ U" := (subty G S U).
Hint Constructors subty.
