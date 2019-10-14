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

Require Export StdSetup.
Require Export VarDef.

Hint Rewrite -> AtomSetProperties.add_union_singleton : meta_ext.

(** * Abstract Syntax *)

(** ** Types
    - [typ_top] represents the [⊤] type.
    - [typ_bot] represents the [⊥] type.
    - [typ_sel x] represents a path dependent type [x.A].
    - [typ_all S U] represents a dependent function type [∀(x: S)U].
    - [typ_bnd S U] represents a type declaration [{ A : S .. U }].
 *)

Inductive typ : Set :=
| typ_top : typ
| typ_bot : typ
| typ_sel : avar -> typ
| typ_all : typ -> typ -> typ
| typ_bnd :  typ -> typ -> typ.
Hint Constructors typ.

Instance EqDecTyp : EqDec_eq typ := { }.
Proof.
  intros; decide equality.
  destruct (a == a0); auto.
Defined.

(** ** Terms and Values
    Terms are represented by the following syntax:
    - [trm_var x] represents variable [x] as a term.
    - [trm_val v] represents value [v] as a term.
    - [trm_app x y] represents a function application, where x is treated to be a function.  
    - [trm_let t u] represents a let binding [let x = t in u].

    Values are represented by the following syntax:
    - [val_bnd T] represents a type tag [{ A = T }].
    - [val_lam T t] represents a lambda expression [λ(x : T) t].
 *)

Inductive trm : Set :=
| trm_var : avar -> trm
| trm_val : val -> trm
| trm_app : avar -> avar -> trm
| trm_let : trm -> trm -> trm
with
val : Set :=
| val_bnd : typ -> val
| val_lam : typ -> trm -> val.

Hint Constructors trm val.

(** * Basic Characteristics

    Here we define some basic characteristics of the abstract syntax, including local
 closure, the opening, closing and substitution operations, and the retrieval of free
 variables of variables, types, terms and values.

 This library uses a number of type classes to capture these characteristics,
 including [LC], [CanOpen], [CanClose] and [HasFv]. Thus, each characteristic can be
 represented by one single predicate.  *)
Section LocalClosure.

  Inductive lc_avar_at : nat -> avar -> Prop :=
  | lc_ab : forall {n m}, n < m -> lc_avar_at m (avar_b n)
  | lc_af : forall {n x}, lc_avar_at n (avar_f x).

  Global Instance LcAvar : LC avar := { lc_at := lc_avar_at }.
  
  Inductive lc_typ_at : nat -> typ -> Prop :=
  | lc_typ_top : forall {n}, lc_typ_at n typ_top
  | lc_typ_bot : forall {n}, lc_typ_at n typ_bot
  | lc_typ_sel : forall {n v}, lc_at n v -> lc_typ_at n (typ_sel v)
  | lc_typ_all : forall {n T U}, lc_typ_at n T -> lc_typ_at (S n) U ->
                            lc_typ_at n (typ_all T U)
  | lc_typ_bnd : forall {n S U}, lc_typ_at n S -> lc_typ_at n U ->
                            lc_typ_at n (typ_bnd S U).

  Global Instance LcTyp : LC typ := { lc_at := lc_typ_at }.

  Inductive lc_trm_at : nat -> trm -> Prop :=
  | lc_trm_var : forall {n v}, lc_at n v -> lc_trm_at n (trm_var v)
  | lc_trm_val : forall {n vl}, lc_val_at n vl -> lc_trm_at n (trm_val vl)
  | lc_trm_app : forall {n x y}, lc_at n x -> lc_at n y -> lc_trm_at n (trm_app x y)
  | lc_trm_let : forall {n t1 t2}, lc_trm_at n t1 -> lc_trm_at (S n) t2 ->
                              lc_trm_at n (trm_let t1 t2)
  with
  lc_val_at : nat -> val -> Prop :=
  | lc_val_bnd : forall {n T}, lc_at n T -> lc_val_at n (val_bnd T)
  | lc_val_lam : forall {n T t}, lc_at n T -> lc_trm_at (S n) t ->
                            lc_val_at n (val_lam T t).

  Global Instance LcTrm : LC trm := { lc_at := lc_trm_at }.
  Global Instance LcVal : LC val := { lc_at := lc_val_at }.
  
End LocalClosure.

Hint Constructors lc_avar_at lc_typ_at lc_trm_at lc_val_at.

Section OpeningDefinitions.
  
  Definition open_rec_avar (k : nat) (u : var) (a : avar) : avar :=
    match a with
    | avar_b i => if k == i then avar_f u else avar_b i
    | avar_f x => avar_f x
    end.

  Fixpoint open_rec_typ (k : nat) (u : var) (T : typ) : typ :=
    match T with
    | typ_top => typ_top
    | typ_bot => typ_bot
    | typ_sel x => typ_sel $ open_rec_avar k u x
    | typ_all T U => typ_all (open_rec_typ k u T) $ open_rec_typ (S k) u U
    | typ_bnd T U => typ_bnd (open_rec_typ k u T) $ open_rec_typ k u U
    end.

  Fixpoint open_rec_trm k u (t : trm) : trm :=
    match t with
    | trm_var x => trm_var $ open_rec_avar k u x
    | trm_val v => trm_val $ open_rec_val k u v
    | trm_app x y => trm_app (open_rec_avar k u x) $ open_rec_avar k u y
    | trm_let s t => trm_let (open_rec_trm k u s) $ open_rec_trm (S k) u t
    end
  with
  open_rec_val k u (vl : val) : val :=
    match vl with
    | val_bnd T => val_bnd $ open_rec_typ k u T
    | val_lam T t => val_lam (open_rec_typ k u T) $ open_rec_trm (S k) u t
    end.

  Global Instance OpenAvar : CanOpen avar := { open_rec := open_rec_avar }.
  Global Instance OpenTyp : CanOpen typ := { open_rec := open_rec_typ }.
  Global Instance OpenTrm : CanOpen trm := { open_rec := open_rec_trm }.
  Global Instance OpenVal : CanOpen val := { open_rec := open_rec_val }.
  
End OpeningDefinitions.

Section ClosingDefinitions.

  Definition close_rec_avar (k : nat) (u : var) (a : avar) : avar :=
    match a with
    | avar_b n => avar_b n
    | avar_f x => if x == u then avar_b k else avar_f x
    end.

  Fixpoint close_rec_typ (k : nat) (u : var) (T : typ) : typ :=
    match T with
    | typ_top => typ_top
    | typ_bot => typ_bot
    | typ_sel x => typ_sel $ close_rec_avar k u x
    | typ_all T U => typ_all (close_rec_typ k u T) $ close_rec_typ (S k) u U
    | typ_bnd T U => typ_bnd (close_rec_typ k u T) $ close_rec_typ k u U
    end.

  Fixpoint close_rec_trm k u (t : trm) : trm :=
    match t with
    | trm_var x => trm_var $ close_rec_avar k u x
    | trm_val v => trm_val $ close_rec_val k u v
    | trm_app x y => trm_app (close_rec_avar k u x) $ close_rec_avar k u y
    | trm_let s t => trm_let (close_rec_trm k u s) $ close_rec_trm (S k) u t
    end
  with
  close_rec_val k u (vl : val) : val :=
    match vl with
    | val_bnd T => val_bnd $ close_rec_typ k u T
    | val_lam T t => val_lam (close_rec_typ k u T) $ close_rec_trm (S k) u t
    end.

  Global Instance CloseAvar : CanClose avar := { close_rec := close_rec_avar }.
  Global Instance CloseTyp : CanClose typ := { close_rec := close_rec_typ }.
  Global Instance CloseTrm : CanClose trm := { close_rec := close_rec_trm }.
  Global Instance CloseVal : CanClose val := { close_rec := close_rec_val }.

End ClosingDefinitions.

Section Substitutions.
  
  Definition subst_avar (z u: var) (a : avar) : avar :=
    match a with
    | avar_b i as a => a
    | avar_f x => avar_f $ if x == z then u else x
    end.

  Fixpoint subst_typ (z u: var) (T : typ) : typ :=
    match T with
    | typ_top => typ_top
    | typ_bot => typ_bot
    | typ_sel x => typ_sel (subst_avar z u x)
    | typ_all T U => typ_all (subst_typ z u T) (subst_typ z u U)
    | typ_bnd T U => typ_bnd (subst_typ z u T) (subst_typ z u U)
    end.

  
  Fixpoint subst_trm (z u: var) (t : trm) : trm :=
    match t with
    | trm_var x => trm_var $ subst_avar z u x
    | trm_val v => trm_val $ subst_val z u v
    | trm_app x y => trm_app (subst_avar z u x) $ subst_avar z u y
    | trm_let t1 t2 => trm_let (subst_trm z u t1) $ subst_trm z u t2
    end
  with
  subst_val (z u: var) (v : val) : val :=
    match v with
    | val_bnd T => val_bnd $ subst_typ z u T
    | val_lam T t => val_lam (subst_typ z u T) (subst_trm z u t)
    end.
  
  Global Instance SubstAvar : CanSubst avar := { substi := subst_avar }.
  Global Instance SubstTyp : CanSubst typ := { substi := subst_typ }.
  Global Instance SubstTrm : CanSubst trm := { substi := subst_trm }.
  Global Instance SubstVal : CanSubst val := { substi := subst_val }.

End Substitutions.

Notation env := (list (var * typ)).

Section FreeVariables.

  Definition fv_avar (v : avar) : vars :=
    match v with
    | avar_b _ => {}
    | avar_f x => {{ x }}
    end.

  Local Ltac empty := exact {}.
  Local Ltac singleton :=
    apply fv_avar; assumption.
  Local Ltac recur f :=
    apply f; assumption.
  Local Ltac recur2 f :=
    lazymatch type of f with
    | forall _: ?T, _ =>
      lazymatch goal with
      | T1 : T, T2 : T |- vars =>
        exact (f T1 \u f T2)
      end
    end.
  
  Fixpoint fv_typ (T : typ) : vars :=
    match T with
    | typ_top | typ_bot => {}
    | typ_sel _ => ltac:(singleton)
    | typ_all _ _ | typ_bnd _ _ => ltac:(recur2 fv_typ)
    end.

  Fixpoint fv_trm (t : trm) : vars :=
    match t with
    | trm_var _ => ltac:(singleton)
    | trm_val _ => ltac:(recur fv_val)
    | trm_app x y => fv_avar x \u fv_avar y
    | trm_let _ _ => ltac:(recur2 fv_trm)
    end
  with
  fv_val (vl : val) : vars :=
    match vl with
    | val_bnd _ => ltac:(recur fv_typ)
    | val_lam T t => fv_typ T \u fv_trm t
    end.

  Global Instance FvAvar : HasFv avar := { fv := fv_avar }.
  Global Instance FvTyp : HasFv typ := { fv := fv_typ }.
  Global Instance FvTrm : HasFv trm := { fv := fv_trm }.
  Global Instance FvVal : HasFv val := { fv := fv_val }.

  Global Instance FvEnv : HasFv env := { fv := fun e => dom e `union` fv_values fv e }.
  
  Lemma fv_union : forall (e1 e2 : env) , fv (e1 ++ e2) [=] fv e1 `union` fv e2.
  Proof.
    intros; simpl. 
    apply AtomSetProperties.subset_antisym;
      set solve.
  Qed.
  
End FreeVariables.

Hint Rewrite -> fv_union : meta_ext.

Ltac gather_atoms ::=
  let A := gather_atoms_with (fun x : atoms => x) in
  let B := gather_atoms_with (fun x : atom => singleton x) in
  let C := gather_atoms_with (fun x : env => fv x) in
  let D := gather_atoms_with fv_avar in
  let E := gather_atoms_with fv_typ in
  let F := gather_atoms_with fv_trm in
  let G := gather_atoms_with fv_val in
  constr:(A `union` B `union` C `union` D `union` E `union` F `union` G).

Reserved Notation "G ⊢ t ⦂ T" (at level 90).
Reserved Notation "G ⊢ S <⦂ U" (at level 90).

(** * Type Assigment and Subtyping
 *)

(** The type assignment judgment [G ⊢ t : T]: *)
Inductive typing : env -> trm -> typ -> Prop :=
(** [――――――――――――] Var #<br>#
    [G ⊢ x : G(x)]  *)
| ty_var : forall {G v T},
    binds v T G ->
    G ⊢ trm_var $ avar_f v ⦂ T
(** [――――――――――――――――――――――――――――――] Typ-I #<br>#
    [G ⊢ { A = T } : { A : T .. T }]  *)
| ty_bnd : forall G T,
    G ⊢ trm_val $ val_bnd T ⦂ typ_bnd T T
(** [G; x : S ⊢ t : U]
    [――――――――――――――――] All-I #<br>#
    [G ⊢ λ(x : S)t : ∀(x : S)U]  *)
| ty_lam : forall {L G S U t},
    (forall x, x \notin L ->
          x ~ S ++ G ⊢ open x t ⦂ open x U) ->
    G ⊢ trm_val $ val_lam S t ⦂ typ_all S U
(** [G ⊢ x : ∀(z : S)U] #<br>#
    [G ⊢ y : S] #<br>#
    [―――――――――――――――――――――――――] All-E #<br>#
    [G ⊢ λ(x : S)t : ∀(x : S)U]  *)
| ty_app : forall {G S U x y},
    G ⊢ trm_var $ avar_f x ⦂ typ_all S U ->
    G ⊢ trm_var $ avar_f y ⦂ S ->
    G ⊢ (trm_app (avar_f x) $ avar_f y) ⦂ open y U
(** [G ⊢ s : S] #<br>#
    [G; x : S ⊢ u : U (x ∉ fv(U))] #<br>#
    [――――――――――――――――――――――――――――] Let #<br>#
    [G ⊢ let x  = s in u : U]  *)
| ty_let : forall {L G s S u U},
    G ⊢ s ⦂ S ->
    (forall x, x \notin L -> x ~ S ++ G ⊢ open x u ⦂ U) ->
    G ⊢ trm_let s u ⦂ U
(** [G ⊢ x : S] #<br>#
    [G ⊢ S <: U] #<br>#
    [――――――――――] Sub #<br>#
    [G ⊢ x : U]  *)
| ty_sub : forall {G t S U},
    G ⊢ t ⦂ S ->
    G ⊢ S <⦂ U ->
    G ⊢ t ⦂ U
where "G ⊢ t ⦂ T" := (typing G t T)
with
(** The subtyping judgment [G ⊢ S <: U]: *)
subty : env -> typ -> typ -> Prop :=
(** [――――――――――] Refl #<br>#
    [G ⊢ T <: T]  *)
| st_refl : forall G T,
    G ⊢ T <⦂ T
(** [――――――――――] Top #<br>#
    [G ⊢ T <: ⊤]  *)
| st_top : forall G T,
    G ⊢ T <⦂ typ_top
(** [――――――――――] Bot #<br>#
    [G ⊢ ⊥ <: T]  *)
| st_bot : forall G T,
    G ⊢ typ_bot <⦂ T
(** [G ⊢ S <: T] #<br>#
    [G ⊢ T <: U] #<br>#
    [――――――――――] Trans #<br>#
    [G ⊢ S <: U]  *)
| st_trans : forall {G S T U},
    G ⊢ S <⦂ T ->
    G ⊢ T <⦂ U ->
    G ⊢ S <⦂ U
(** [G ⊢ S <: T1] #<br>#
    [G ⊢ T2 <: U] #<br>#
    [――――――――――――――――――――――――――――――――――――――] Bnd #<br>#
    [G ⊢ { A : T1 .. T2 } <: { A : S .. U }]  *)
| st_bnd : forall {G S T1 T2 U},
    G ⊢ S <⦂ T1 ->
    G ⊢ T2 <⦂ U ->
    G ⊢ typ_bnd T1 T2 <⦂ typ_bnd S U
(** [G ⊢ S2 <: S1] #<br>#
    [G; x : S2 ⊢ U1 <: U2] #<br>#
    [――――――――――――――――――――――――――――――] All #<br>#
    [G ⊢ ∀(x : S1)U1 <: ∀(x : S2)U2]  *)
| st_all : forall {L G S1 S2 U1 U2},
    G ⊢ S2 <⦂ S1 ->
    (forall x, x \notin L -> x ~ S2 ++ G ⊢ open x U1 <⦂ open x U2) ->
    G ⊢ typ_all S1 U1 <⦂ typ_all S2 U2
(** [G ⊢ x <: { A : S .. U }] #<br>#
    [―――――――――――――――――――――――] Sel1 #<br>#
    [G ⊢ S <: x.A]  *)
| st_sel1 : forall {G x S U},
    G ⊢ trm_var $ avar_f x ⦂ typ_bnd S U ->
    G ⊢ S <⦂ typ_sel $ avar_f x
(** [G ⊢ x <: { A : S .. U }] #<br>#
    [―――――――――――――――――――――――] Sel2 #<br>#
    [G ⊢ x.A <: U]  *)
| st_sel2 : forall {G x S U},
    G ⊢ trm_var $ avar_f x ⦂ typ_bnd S U ->
    G ⊢ typ_sel $ avar_f x <⦂ U
where "G ⊢ S <⦂ U" := (subty G S U).
Hint Constructors typing subty.
(** removing this rule from hintbase to avoid unexpected subsumption. *)
Remove Hints ty_sub.
