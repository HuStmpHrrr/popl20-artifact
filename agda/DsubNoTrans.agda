{-# OPTIONS --without-K --safe #-}

-- This module shows that D<: subtyping without transitivity, or equivalently, without
-- bad bounds, remains undecidable.
module DsubNoTrans where

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
open import Induction.Nat

open import DsubDef
open import DsubReduced
open import FsubMinus
open import FsubMinus2
open import Utils

infix 4 _⊢_<:_
data _⊢_<:_ : Env → Typ → Typ → Set where
  <:⊤  : ∀ {Γ T} → Γ ⊢ T <: ⊤
  ⊥<:  : ∀ {Γ T} → Γ ⊢ ⊥ <: T
  refl : ∀ {Γ T} → Γ ⊢ T <: T
  bnd  : ∀ {Γ S U S′ U′} →
           Γ ⊢ S′ <: S →
           Γ ⊢ U <: U′ →
           Γ ⊢ ⟨A: S ⋯ U ⟩ <: ⟨A: S′ ⋯ U′ ⟩
  Π<:  : ∀ {Γ S U S′ U′} →
           Γ ⊢ S′ <: S →
           Γ ‣ S′ ! ⊢ U <: U′ →
           Γ ⊢ Π S ∙ U <: Π S′ ∙ U′
  sel₁ : ∀ {Γ n T S} →
           env-lookup Γ n ≡ just T →
           Γ ⊢ T <: ⟨A: S ⋯ ⊤ ⟩ →
           Γ ⊢ S <: n ∙A
  sel₂ : ∀ {Γ n T U} →
           env-lookup Γ n ≡ just T →
           Γ ⊢ T <: ⟨A: ⊥ ⋯ U ⟩ →
           Γ ⊢ n ∙A <: U

module Contravariant where
  open InvertibleProperties contraInvertible _⊢_<:_ public

  D⇒Dᵢ : ∀ {Γ S U} → Γ ⊢ S <: U → ContraEnv Γ → Γ ⊢ᵢ S <: U
  D⇒Dᵢ <:⊤ all                        = ditop
  D⇒Dᵢ ⊥<: all                        = dibot
  D⇒Dᵢ refl all                       = direfl
  D⇒Dᵢ (bnd S′<:S U<:U′) all          = dibnd (D⇒Dᵢ S′<:S all) (D⇒Dᵢ U<:U′ all)
  D⇒Dᵢ (Π<: S′<:S U<:U′) all          = diall (D⇒Dᵢ S′<:S all) U<:U′
  D⇒Dᵢ (sel₁ T∈Γ S<:U) all with lookupContraEnv T∈Γ all
  ... | ctt _ with ⟨A:⟩<:⟨A:⟩ (D⇒Dᵢ S<:U all) all
  ...            | S<:⊥ , _ with <:⊥ S<:⊥ all
  ...                          | refl = dibot
  D⇒Dᵢ (sel₂ T∈Γ S<:U) all with lookupContraEnv T∈Γ all
  ... | ctt _ with ⟨A:⟩<:⟨A:⟩ (D⇒Dᵢ S<:U all) all
  ...            | _ , U′<:U          = ditrans _ (disel T∈Γ) U′<:U

module Undecidability′ where
  open FsubMinusToDsubR
  open Contravariant hiding (Π<:)

  ⟨A:⊥⟩<:-lb : ∀ {Γ T S U} → Γ ⊢ ⟨A: ⊥ ⋯ T ⟩ <: ⟨A: S ⋯ U ⟩ → ContraEnv Γ → S ≡ ⊥
  ⟨A:⊥⟩<:-lb D cΓ with ⟨A:⟩<:⟨A:⟩ (D⇒Dᵢ D cΓ) cΓ
  ... | S<:⊥ , _  with <:⊥ S<:⊥ cΓ
  ...                | S≡⊥ = S≡⊥

  <:⇒<:ᵣ : ∀ {Γ S U} →
              Γ ⊢ S <: U →
              ContraEnv Γ → Covar S → Covar U →
              Γ ⊢ᵣ S <: U
  <:⇒<:ᵣ <:⊤ cΓ cS cU                                           = drtop cS
  <:⇒<:ᵣ ⊥<: cΓ () cU
  <:⇒<:ᵣ refl cΓ cS cU                                          = drrefl cU
  <:⇒<:ᵣ (bnd S′<:S U<:U′) cΓ cS ()
  <:⇒<:ᵣ (Π<: <:⊤ U<:U′) cΓ () cU
  <:⇒<:ᵣ (Π<: ⊥<: U<:U′) cΓ cS ()
  <:⇒<:ᵣ (Π<: refl U<:U′) cΓ (cvΠ cS cU) (cvΠ cS′ cU′)          = drall cS′ cU cS′ cU′
                                                                        (drrefl cS′)
                                                                        (<:⇒<:ᵣ U<:U′ (ctt cS′ ∷ cΓ) cU cU′)
  <:⇒<:ᵣ (Π<: (bnd _ S′<:S) U<:U′) cΓ (cvΠ cS cU) (cvΠ cS′ cU′) = drall cS cU cS′ cU′
                                                                        (<:⇒<:ᵣ S′<:S cΓ cS′ cS)
                                                                        (<:⇒<:ᵣ U<:U′ (ctt cS′ ∷ cΓ) cU cU′)
  <:⇒<:ᵣ (Π<: (Π<: S′<:S S′<:S₁) U<:U′) cΓ () cU
  <:⇒<:ᵣ (Π<: (sel₁ x S′<:S) U<:U′) cΓ () cU
  <:⇒<:ᵣ (Π<: (sel₂ x S′<:S) U<:U′) cΓ cS ()
  <:⇒<:ᵣ (sel₁ T∈Γ T<:B) cΓ cS cU
    with lookupContraEnv T∈Γ cΓ
  ... | ctt _  with ⟨A:⊥⟩<:-lb T<:B cΓ
  ...             | refl                                        = case cS of λ ()
  <:⇒<:ᵣ (sel₂ T∈Γ T<:B) cΓ cS cU
    with lookupContraEnv T∈Γ cΓ
  ... | ctt cT                                                  = drsel T∈Γ cT (aux T<:B cΓ cT cU)
    where aux : ∀ {Γ T S U} → Γ ⊢ ⟨A: ⊥ ⋯ T ⟩ <: ⟨A: S ⋯ U ⟩ → ContraEnv Γ → Covar T → Covar U → Γ ⊢ᵣ T <: U
          aux refl cΓ cT cU         = drrefl cU
          aux (bnd _ T<:U) cΓ cT cU = <:⇒<:ᵣ T<:U cΓ cT cU

  <:ᵣ⇒<: : ∀ {Γ S U} → Γ ⊢ᵣ S <: U → Γ ⊢ S <: U
  <:ᵣ⇒<: (drtop _)                   = <:⊤
  <:ᵣ⇒<: (drrefl _)                  = refl
  <:ᵣ⇒<: (drall _ _ _ _ S′<:S U<:U′) = Π<: (bnd ⊥<: (<:ᵣ⇒<: S′<:S)) (<:ᵣ⇒<: U<:U′)
  <:ᵣ⇒<: (drsel T∈Γ _ T<:B)          = sel₂ T∈Γ (bnd ⊥<: (<:ᵣ⇒<: T<:B))

  open FsubMinus.FsubMinus

  F<:⇒D<: : ∀ {Γ S U} → Γ ⊢F S <: U → ⟪ Γ ⟫ ⊢ ⟦ S ⟧ <: ⟦ U ⟧
  F<:⇒D<: = <:ᵣ⇒<: ∘ F<:⇒D<:ᵣ

  D<:⇒F<: : ∀ {Γ S U} → ⟪ Γ ⟫ ⊢ ⟦ S ⟧ <: ⟦ U ⟧ → Γ ⊢F S <: U
  D<:⇒F<: S<:U = D<:ᵣ⇒F<: (<:⇒<:ᵣ S<:U (⟪⟫-contraEnv _) (⟦⟧-covar _) (⟦⟧-covar _))
                          refl refl refl
