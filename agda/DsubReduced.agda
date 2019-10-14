{-# OPTIONS --without-K --safe #-}

-- This module defines an intermediate calculus that is set up in the D<: universe
-- which bridges F<:- and D<:. The goal here is purely technical - to simply reduce
-- duplication.
module DsubReduced where

open import Data.List as List
open import Data.List.All as All
open import Data.Nat as ℕ
open import Data.Maybe as Maybe
open import Data.Product
open import Function

open import Data.Maybe.Properties as Maybeₚ
open import Data.Nat.Properties as ℕₚ
open import Relation.Nullary
open import Relation.Binary.PropositionalEquality as ≡

open import DsubDef
open import FsubMinus
open import FsubMinus2
open import Utils

-- D<: Reduced
--
-- This judgment for contexts and types in D<: defines a corresponding calculus after
-- interpreting F<:⁻ into D<:. That is, D<: reduced is the image derivation of
-- interpreting F<:⁻ in D<:.
infix 4 _⊢ᵣ_<:_
data _⊢ᵣ_<:_ : Env → Typ → Typ → Set where
  drtop   : ∀ {Γ T} → Covar T → Γ ⊢ᵣ T <: ⊤
  drrefl  : ∀ {Γ T} → Covar T → Γ ⊢ᵣ T <: T
  drall   : ∀ {Γ S U S′ U′} →
              Covar S → Covar U → Covar S′ → Covar U′ →
              (S′<:S : Γ ⊢ᵣ S′ <: S) →
              (U<:U′ : ⟨A: ⊥ ⋯ S′ ⟩ ∷ Γ ⊢ᵣ U <: U′) →
              Γ ⊢ᵣ Π ⟨A: ⊥ ⋯ S ⟩ ∙ U <: Π ⟨A: ⊥ ⋯ S′ ⟩ ∙ U′
  drsel   : ∀ {Γ n U U′} →
              (T∈Γ : env-lookup Γ n ≡ just ⟨A: ⊥ ⋯ U ⟩) →
              Covar U →
              Γ ⊢ᵣ U <: U′ →
              Γ ⊢ᵣ n ∙A <: U′


module FsubMinusToDsubR where
  open FsubMinus.FsubMinus renaming (Env to Env′ ; _↑_ to _⇑_) hiding (env-lookup)

  infix 5 ⟦_⟧ ⟪_⟫
  ⟦_⟧ : Ftyp → Typ
  ⟦ ⊤ ⟧         = ⊤
  ⟦ var x ⟧     = x ∙A
  ⟦ Π<: S ∙ U ⟧ = Π ⟨A: ⊥ ⋯ ⟦ S ⟧ ⟩ ∙ ⟦ U ⟧

  ⟪_⟫ : Env′ → Env
  ⟪ [] ⟫    = []
  ⟪ T ∷ Γ ⟫ = ⟨A: ⊥ ⋯ ⟦ T ⟧ ⟩ ∷ ⟪ Γ ⟫

  module ⟦⟧-Bijective where
    open import Function.Bijection
    open import Function.Surjection
    open import Function.Equality

    CovTyp : Set
    CovTyp = ∃ λ T → Covar T

    ⟦⟧-covar : ∀ T → Covar ⟦ T ⟧
    ⟦⟧-covar ⊤           = cv⊤
    ⟦⟧-covar (var x)     = cv∙A _
    ⟦⟧-covar (Π<: S ∙ U) = cvΠ (⟦⟧-covar S) (⟦⟧-covar U)

    ⟦⟧-func : ≡.setoid Ftyp ⟶ ≡.setoid CovTyp
    ⟦⟧-func   = record
      { _⟨$⟩_ = < ⟦_⟧ , ⟦⟧-covar >
      ; cong  = ≡.cong < ⟦_⟧ , ⟦⟧-covar >
      }

    ⟦⟧-injective : ∀ {S U} → ⟦ S ⟧ ≡ ⟦ U ⟧ → S ≡ U
    ⟦⟧-injective {⊤} {⊤} eq            = refl
    ⟦⟧-injective {⊤} {var x} ()
    ⟦⟧-injective {⊤} {Π<: _ ∙ _} ()
    ⟦⟧-injective {var x} {⊤} ()
    ⟦⟧-injective {var x} {var .x} refl = refl
    ⟦⟧-injective {var x} {Π<: _ ∙ _} ()
    ⟦⟧-injective {Π<: _ ∙ _} {⊤} ()
    ⟦⟧-injective {Π<: _ ∙ _} {var x} ()
    ⟦⟧-injective {Π<: S₁ ∙ U₁} {Π<: S₂ ∙ U₂} eq
      with ⟦ S₁ ⟧ | ⟦ S₂ ⟧ | ⟦ U₁ ⟧ | ⟦ U₂ ⟧
         | ⟦⟧-injective {S₁} {S₂} | ⟦⟧-injective {U₁} {U₂}
    ⟦⟧-injective {Π<: S₁ ∙ U₁} {Π<: S₂ ∙ U₂} refl
         | _ | _ | _ | _ | rec₁ | rec₂ = ≡.cong₂ Π<:_∙_ (rec₁ refl) (rec₂ refl)

    ⟦⟧-func-injective : ∀ {S U} → (CovTyp ∋ (⟦ S ⟧ , ⟦⟧-covar S)) ≡ (⟦ U ⟧ , ⟦⟧-covar U) → S ≡ U
    ⟦⟧-func-injective {S} {U} eq
      with ⟦ S ⟧ | ⟦⟧-covar S | ⟦ U ⟧ | ⟦⟧-covar U
         | ⟦⟧-injective {S} {U}
    ⟦⟧-func-injective {S} {U} refl
         | _ | _ | _ | _ | inj = inj refl

    infix 5 ⟦_⟧⁻¹
    ⟦_⟧⁻¹ : CovTyp → Ftyp
    ⟦ _ , cv⊤ ⟧⁻¹     = ⊤
    ⟦ _ , cv∙A x ⟧⁻¹  = var x
    ⟦ _ , cvΠ S U ⟧⁻¹ = Π<: ⟦ -, S ⟧⁻¹ ∙ ⟦ -, U ⟧⁻¹

    ⟦⟧-func-inv : ≡.setoid CovTyp ⟶ ≡.setoid Ftyp
    ⟦⟧-func-inv = record
      { _⟨$⟩_   = ⟦_⟧⁻¹
      ; cong    = ≡.cong ⟦_⟧⁻¹
      }

    ⟦⟧-left-inverse-⟦⟧⁻¹ : ∀ {T} (cT : Covar T) → (⟦ ⟦ -, cT ⟧⁻¹ ⟧ , ⟦⟧-covar ⟦ -, cT ⟧⁻¹) ≡ (CovTyp ∋ (-, cT))
    ⟦⟧-left-inverse-⟦⟧⁻¹ cv⊤           = refl
    ⟦⟧-left-inverse-⟦⟧⁻¹ (cv∙A n)      = refl
    ⟦⟧-left-inverse-⟦⟧⁻¹ (cvΠ S U)
      with ⟦ ⟦ -, S ⟧⁻¹ ⟧         | ⟦ ⟦ -, U ⟧⁻¹ ⟧ 
         | ⟦⟧-covar ⟦ -, S ⟧⁻¹    | ⟦⟧-covar ⟦ -, U ⟧⁻¹
         | ⟦⟧-left-inverse-⟦⟧⁻¹ S | ⟦⟧-left-inverse-⟦⟧⁻¹ U
    ...  | _ | _ | _ | _ | refl | refl = refl

    ⟦⟧-bijective : Bijective ⟦⟧-func
    ⟦⟧-bijective   = record
      { injective  = ⟦⟧-func-injective
      ; surjective = record
        { from             = ⟦⟧-func-inv
        ; right-inverse-of = λ { (_ , T) → ⟦⟧-left-inverse-⟦⟧⁻¹ T }
        }
      }

  open ⟦⟧-Bijective using (⟦⟧-covar ; ⟦⟧-injective) public

  ⟪⟫-contraEnv : ∀ Γ → ContraEnv ⟪ Γ ⟫
  ⟪⟫-contraEnv []      = []
  ⟪⟫-contraEnv (T ∷ Γ) = ctt (⟦⟧-covar T) ∷ ⟪⟫-contraEnv Γ

  ⟦⟧-↑-comm : ∀ T n → ⟦ T ⟧ ↑ n ≡ ⟦ T ⇑ n ⟧
  ⟦⟧-↑-comm ⊤ n = refl
  ⟦⟧-↑-comm (var x) n with n ≤? x
  ... | yes n≤x = refl
  ... | no n>x  = refl
  ⟦⟧-↑-comm (Π<: S ∙ U) n
    rewrite ⟦⟧-↑-comm S n | ⟦⟧-↑-comm U (suc n)
                = refl

  <:∈⇒env-lookup : ∀ {n T Γ} → n <: T ∈ Γ → env-lookup ⟪ Γ ⟫ n ≡ just ⟨A: ⊥ ⋯ ⟦ T ⟧ ⟩
  <:∈⇒env-lookup {_} {_} {T ∷ ._} hd
    rewrite ⟦⟧-↑-comm T 0       = refl
  <:∈⇒env-lookup {suc n} {_} {._ ∷ Γ} (tl {_} {T} T∈Γ)
    with lookupOpt ⟪ Γ ⟫ n | <:∈⇒env-lookup T∈Γ
  ...  | nothing           | ()
  ...  | just _            | eq
    rewrite sym $ ⟦⟧-↑-comm T 0 = cong (just ∘ (_↑ 0)) (just-injective eq)

  F<:⇒D<:ᵣ : ∀ {Γ S U} → Γ ⊢F S <: U → ⟪ Γ ⟫ ⊢ᵣ ⟦ S ⟧ <: ⟦ U ⟧
  F<:⇒D<:ᵣ ftop               = drtop (⟦⟧-covar _)
  F<:⇒D<:ᵣ fvrefl             = drrefl (cv∙A _)
  F<:⇒D<:ᵣ (fbinds T∈Γ T<:U)  = drsel (<:∈⇒env-lookup T∈Γ) (⟦⟧-covar _) (F<:⇒D<:ᵣ T<:U)
  F<:⇒D<:ᵣ (fall S′<:S U<:U′) = drall (⟦⟧-covar _) (⟦⟧-covar _) (⟦⟧-covar _) (⟦⟧-covar _)
                                      (F<:⇒D<:ᵣ S′<:S) (F<:⇒D<:ᵣ U<:U′)

  env-lookup⇒<:∈ : ∀ {n T Γ} → env-lookup Γ n ≡ just ⟨A: ⊥ ⋯ T ⟩ →
                   ∀ {Γ′} → Γ ≡ ⟪ Γ′ ⟫ →
                   ∃ λ T′ → T ≡ ⟦ T′ ⟧ × n <: T′ ∈ Γ′
  env-lookup⇒<:∈ T∈Γ eqΓ = aux (lookup⇒↦∈ T∈Γ) refl eqΓ
    where aux : ∀ {n T Γ} → n ↦ T ∈ Γ →
                   ∀ {U Γ′} → T ≡ ⟨A: ⊥ ⋯ U ⟩ → Γ ≡ ⟪ Γ′ ⟫ →
                   ∃ λ U′ → U ≡ ⟦ U′ ⟧ × n <: U′ ∈ Γ′
          aux hd {_} {[]} eqT ()
          aux hd {_} {T ∷ Γ′} refl refl
            rewrite ⟦⟧-↑-comm T 0 = T ⇑ zero , refl , hd
          aux (tl T∈Γ) {_} {[]} eqT ()
          aux (tl {T = ⊤} T∈Γ) {_} {_ ∷ Γ′} () refl
          aux (tl {T = ⊥} T∈Γ) {_} {_ ∷ Γ′} () refl
          aux (tl {T = n ∙A} T∈Γ) {_} {_ ∷ Γ′} () refl
          aux (tl {T = Π S ∙ U} T∈Γ) {_} {_ ∷ Γ′} () refl
          aux (tl {T = ⟨A: ⊤ ⋯ U ⟩} T∈Γ) {_} {_ ∷ Γ′} () refl
          aux (tl {T = ⟨A: ⊥ ⋯ U ⟩} T∈Γ) {_} {_ ∷ Γ′} refl refl
            with aux T∈Γ refl refl
          ...  | U′ , refl , U′∈Γ′
            rewrite ⟦⟧-↑-comm U′ 0 = U′ ⇑ zero , refl , tl U′∈Γ′
          aux (tl {T = ⟨A: _ ∙A ⋯ U ⟩} T∈Γ) {_} {_ ∷ Γ′} () refl
          aux (tl {T = ⟨A: Π _ ∙ _ ⋯ U ⟩} T∈Γ) {_} {_ ∷ Γ′} () refl
          aux (tl {T = ⟨A: ⟨A: _ ⋯ _ ⟩ ⋯ U ⟩} T∈Γ) {_} {_ ∷ Γ′} () refl

  D<:ᵣ⇒F<: : ∀ {Γ′ S′ U′} → Γ′ ⊢ᵣ S′ <: U′ →
            ∀ {Γ S U} →
              Γ′ ≡ ⟪ Γ ⟫ → S′ ≡ ⟦ S ⟧ → U′ ≡ ⟦ U ⟧ →
              Γ ⊢F S <: U
  D<:ᵣ⇒F<: (drtop S′) {Γ} {S} {⊤} eqΓ eqS refl   = ftop
  D<:ᵣ⇒F<: (drtop S′) {Γ} {S} {var x} eqΓ eqS ()
  D<:ᵣ⇒F<: (drtop S′) {Γ} {S} {Π<: U ∙ U₁} eqΓ eqS ()
  D<:ᵣ⇒F<: (drrefl S′) {Γ} {S} {U} eqΓ eqS eqU
    rewrite ⟦⟧-injective (≡.trans (sym eqS) eqU) = <:-refl Γ U
  D<:ᵣ⇒F<: (drall cS cU cS′ cU′ S′<:S U<:U′) {Γ} {⊤} {⊤} eqΓ () eqU
  D<:ᵣ⇒F<: (drall cS cU cS′ cU′ S′<:S U<:U′) {Γ} {⊤} {var x} eqΓ () eqU
  D<:ᵣ⇒F<: (drall cS cU cS′ cU′ S′<:S U<:U′) {Γ} {⊤} {Π<: U ∙ U₁} eqΓ () eqU
  D<:ᵣ⇒F<: (drall cS cU cS′ cU′ S′<:S U<:U′) {Γ} {var _} {⊤} eqΓ () eqU
  D<:ᵣ⇒F<: (drall cS cU cS′ cU′ S′<:S U<:U′) {Γ} {var _} {var _} eqΓ () eqU
  D<:ᵣ⇒F<: (drall cS cU cS′ cU′ S′<:S U<:U′) {Γ} {var _} {Π<: _ ∙ _} eqΓ () eqU
  D<:ᵣ⇒F<: (drall cS cU cS′ cU′ S′<:S U<:U′) {Γ} {Π<: _ ∙ _} {⊤} eqΓ refl ()
  D<:ᵣ⇒F<: (drall cS cU cS′ cU′ S′<:S U<:U′) {Γ} {Π<: _ ∙ _} {var _} eqΓ refl ()
  D<:ᵣ⇒F<: (drall cS cU cS′ cU′ S′<:S U<:U′) {Γ} {Π<: S ∙ U} {Π<: S′ ∙ U′} eqΓ refl refl
    = fall (D<:ᵣ⇒F<: S′<:S eqΓ refl refl)
           (D<:ᵣ⇒F<: U<:U′ (cong (⟨A: ⊥ ⋯ ⟦ S′ ⟧ ⟩ ∷_) eqΓ) refl refl)
  D<:ᵣ⇒F<: (drsel T∈Γ cT S<:U) {Γ} {⊤} {U} eqΓ () eqU
  D<:ᵣ⇒F<: (drsel T∈Γ cT S<:U) {Γ} {var x} {U} eqΓ refl eqU
    with env-lookup⇒<:∈ T∈Γ eqΓ
  ...  | U′ , eqU′ , T′∈Γ = fbinds T′∈Γ (D<:ᵣ⇒F<: S<:U eqΓ eqU′ eqU)
  D<:ᵣ⇒F<: (drsel T∈Γ cT S<:U) {Γ} {Π<: _ ∙ _} {U} eqΓ () eqU
