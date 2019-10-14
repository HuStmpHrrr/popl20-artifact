{-# OPTIONS --without-K --safe #-}

-- In this module, we define the usual definition of D<: -- the one having typing and
-- subtyping mutually defined.
module DsubFull where

open import Data.List as List
open import Data.List.All as All
open import Data.Nat as ℕ
open import Data.Maybe as Maybe
open import Data.Product
open import Data.Sum
open import Data.Empty renaming (⊥ to False)
open import Data.Vec as Vec renaming (_∷_ to _‼_ ; [] to nil) hiding (_++_)
open import Function

open import Data.Maybe.Properties as Maybeₚ
open import Data.Nat.Properties as ℕₚ
open import Relation.Nullary
open import Relation.Binary.PropositionalEquality as ≡

open import DsubDef
open import Dsub renaming (_⊢_<:_ to _⊢′_<:_)
open import Utils

infix 4 _⊢_<:_ _⊢_∶_
  
mutual
  data _⊢_∶_ : Env → Trm → Typ → Set where
    var∶  : ∀ {Γ n T} →
      (T∈Γ : env-lookup Γ n ≡ just T) →
      Γ ⊢ var n ∶ T
    Π-I   : ∀ {Γ T t U} →
      Γ ‣ T ! ⊢ t ∶ U →
      Γ ⊢ val (Λ T ∙ t) ∶ Π T ∙ U
    Π-E   : ∀ {Γ n m S U} →
      Γ ⊢ var n ∶ Π S ∙ U →
      Γ ⊢ var m ∶ S →
      Γ ⊢ n $$ m ∶ U [ m / 0 ]
    ⟨A⟩-I : ∀ {Γ T} →
      Γ ⊢ val ⟨A= T ⟩ ∶ ⟨A: T ⋯ T ⟩
    ltinn : ∀ {Γ t u T U} →
      Γ ⊢ t ∶ T →
      Γ ‣ T ! ⊢ u ∶ U ↑ 0 →
      Γ ⊢ lt t inn u ∶ U
    <∶   : ∀ {Γ t S U} →
      Γ ⊢ t ∶ S →
      Γ ⊢ S <: U →
      Γ ⊢ t ∶ U    

  data _⊢_<:_ : Env → Typ → Typ → Set where
    <:⊤   : ∀ {Γ T} →
      Γ ⊢ T <: ⊤
    ⊥<:   : ∀ {Γ T} →
      Γ ⊢ ⊥ <: T
    refl  : ∀ {Γ T} →
      Γ ⊢ T <: T
    tran : ∀ {Γ S U} T →
      (S<:T : Γ ⊢ S <: T) →
      (T<:U : Γ ⊢ T <: U) →
      Γ ⊢ S <: U
    bnd   : ∀ {Γ S U S′ U′} →
      (S′<:S : Γ ⊢ S′ <: S) →
      (U<:U′ : Γ ⊢ U <: U′) →
      Γ ⊢ ⟨A: S ⋯ U ⟩ <: ⟨A: S′ ⋯ U′ ⟩
    Π<:   : ∀ {Γ S U S′ U′} →
      (S′<:S : Γ ⊢ S′ <: S) →
      (U<:U′ : (S′ ∷ Γ) ⊢ U <: U′) →
      Γ ⊢ Π S ∙ U <: Π S′ ∙ U′
    sel₁  : ∀ {Γ n S U} →
      Γ ⊢ var n ∶ ⟨A: S ⋯ U ⟩ →
      Γ ⊢ S <: n ∙A
    sel₂  : ∀ {Γ n S U} →
      Γ ⊢ var n ∶ ⟨A: S ⋯ U ⟩ →
      Γ ⊢ n ∙A <: U

-- The following function shows that indeed the subtyping defined in Lemma 2 is
-- equivalent to the original subtyping.
mutual
  <:⇒<:′ : ∀ {Γ S U} → Γ ⊢ S <: U → Γ ⊢′ S <: U
  <:⇒<:′ <:⊤                = dtop
  <:⇒<:′ ⊥<:                = dbot
  <:⇒<:′ refl               = drefl
  <:⇒<:′ (tran T S<:T T<:U) = dtrans T (<:⇒<:′ S<:T) (<:⇒<:′ T<:U)
  <:⇒<:′ (bnd S′<:S U<:U′)  = dbnd (<:⇒<:′ S′<:S) (<:⇒<:′ U<:U′)
  <:⇒<:′ (Π<: S′<:S U<:U′)  = dall (<:⇒<:′ S′<:S) (<:⇒<:′ U<:U′)
  <:⇒<:′ (sel₁ n∶SU) with var∶⇒<: n∶SU
  ... | T′ , T′∈Γ , T′<:SU  = dsel₁ T′∈Γ (dtrans _ T′<:SU (dbnd drefl dtop))
  <:⇒<:′ (sel₂ n∶SU) with var∶⇒<: n∶SU
  ... | T′ , T′∈Γ , T′<:SU  = dsel₂ T′∈Γ (dtrans _ T′<:SU (dbnd dbot drefl))

  var∶⇒<: : ∀ {Γ x T} → Γ ⊢ var x ∶ T → ∃ λ T′ → env-lookup Γ x ≡ just T′ × Γ ⊢′ T′ <: T
  var∶⇒<: (var∶ T∈Γ)      = -, T∈Γ , drefl
  var∶⇒<: (<∶ x∶T T<:U) with var∶⇒<: x∶T
  ... | T′ , T′∈Γ , T′<:T = T′ , T′∈Γ , dtrans _ T′<:T (<:⇒<:′ T<:U)

<:′⇒<: : ∀ {Γ S U} → Γ ⊢′ S <: U → Γ ⊢ S <: U
<:′⇒<: dtop                 = <:⊤
<:′⇒<: dbot                 = ⊥<:
<:′⇒<: drefl                = refl
<:′⇒<: (dtrans T S<:T T<:U) = tran T (<:′⇒<: S<:T) (<:′⇒<: T<:U)
<:′⇒<: (dbnd S′<:S U<:U′)   = bnd (<:′⇒<: S′<:S) (<:′⇒<: U<:U′)
<:′⇒<: (dall S′<:S U<:U′)   = Π<: (<:′⇒<: S′<:S) (<:′⇒<: U<:U′)
<:′⇒<: (dsel₁ T∈Γ T<:SU)    = sel₁ (<∶ (var∶ T∈Γ) (<:′⇒<: T<:SU))
<:′⇒<: (dsel₂ T∈Γ T<:SU)    = sel₂ (<∶ (var∶ T∈Γ) (<:′⇒<: T<:SU))
