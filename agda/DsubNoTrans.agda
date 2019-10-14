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

module DsubNoTrans where

  infix 4 _⊢_<:_

  data _⊢_<:_ : Env → Typ → Typ → Set where
    dtop   : ∀ {Γ T} →
      Γ ⊢ T <: ⊤
    dbot   : ∀ {Γ T} →
      Γ ⊢ ⊥ <: T
    drefl  : ∀ {Γ T} →
      Γ ⊢ T <: T
    dbnd   : ∀ {Γ S U S′ U′} →
      (S′<:S : Γ ⊢ S′ <: S) →
      (U<:U′ : Γ ⊢ U <: U′) →
      Γ ⊢ ⟨A: S ⋯ U ⟩ <: ⟨A: S′ ⋯ U′ ⟩
    dall   : ∀ {Γ S U S′ U′} →
      (S′<:S : Γ ⊢ S′ <: S) →
      (U<:U′ : S′ ∷ Γ ⊢ U <: U′) →
      Γ ⊢ Π S ∙ U <: Π S′ ∙ U′
    dsel₁  : ∀ {Γ n T S} →
      (T∈Γ : env-lookup Γ n ≡ just T) →
      (D : Γ ⊢ T <: ⟨A: S ⋯ ⊤ ⟩) →
      Γ ⊢ S <: n ∙A
    dsel₂  : ∀ {Γ n T U} →
      (T∈Γ : env-lookup Γ n ≡ just T) →
      (D : Γ ⊢ T <: ⟨A: ⊥ ⋯ U ⟩) →
      Γ ⊢ n ∙A <: U

  D-measure : ∀ {Γ S U} (D : Γ ⊢ S <: U) → ℕ
  D-measure dtop          = 1
  D-measure dbot          = 1
  D-measure drefl         = 1
  D-measure (dbnd D₁ D₂)  = 1 + D-measure D₁ + D-measure D₂
  D-measure (dall Dp Db)  = 1 + D-measure Dp + D-measure Db
  D-measure (dsel₁ T∈Γ D) = 1 + D-measure D
  D-measure (dsel₂ T∈Γ D) = 1 + D-measure D

  D-measure≥1 : ∀ {Γ S U} (D : Γ ⊢ S <: U) → D-measure D ≥ 1
  D-measure≥1 dtop        = s≤s z≤n
  D-measure≥1 dbot        = s≤s z≤n
  D-measure≥1 drefl       = s≤s z≤n
  D-measure≥1 (dbnd _ _)  = s≤s z≤n
  D-measure≥1 (dall _ _)  = s≤s z≤n
  D-measure≥1 (dsel₁ _ _) = s≤s z≤n
  D-measure≥1 (dsel₂ _ _) = s≤s z≤n

  D-deriv : Set
  D-deriv = Σ (Env × Typ × Typ) λ { (Γ , S , U) → Γ ⊢ S <: U }

  env : D-deriv → Env
  env ((Γ , _) , _) = Γ

  typ₁ : D-deriv → Typ
  typ₁ ((_ , S , U) , _) = S

  typ₂ : D-deriv → Typ
  typ₂ ((_ , S , U) , _) = U

  D-measure-pack : D-deriv → ℕ
  D-measure-pack (_ , D) = D-measure D

open DsubNoTrans public

module Contravariant where
  open InvertibleProperties contraInvertible _⊢_<:_ public

  D⇒Dᵢ : ∀ {Γ S U} → Γ ⊢ S <: U → ContraEnv Γ → Γ ⊢ᵢ S <: U
  D⇒Dᵢ dtop all                       = ditop
  D⇒Dᵢ dbot all                       = dibot
  D⇒Dᵢ drefl all                      = direfl
  D⇒Dᵢ (dbnd S′<:S U<:U′) all         = dibnd (D⇒Dᵢ S′<:S all) (D⇒Dᵢ U<:U′ all)
  D⇒Dᵢ (dall S′<:S U<:U′) all         = diall (D⇒Dᵢ S′<:S all) U<:U′
  D⇒Dᵢ (dsel₁ T∈Γ S<:U) all with lookupContraEnv T∈Γ all
  ... | ctt _ with ⟨A:⟩<:⟨A:⟩ (D⇒Dᵢ S<:U all) all
  ...            | S<:⊥ , _ with <:⊥ S<:⊥ all
  ...                          | refl = dibot
  D⇒Dᵢ (dsel₂ T∈Γ S<:U) all with lookupContraEnv T∈Γ all
  ... | ctt _ with ⟨A:⟩<:⟨A:⟩ (D⇒Dᵢ S<:U all) all
  ...            | _ , U′<:U          = ditrans _ (disel T∈Γ) U′<:U

module Reduction where
  open FsubMinusToDsubR
  open Contravariant
  
  upper-bound-extract : ∀ {Γ S S′ U U′} →
                          Γ ⊢ ⟨A: S ⋯ U ⟩ <: ⟨A: S′ ⋯ U′ ⟩ →
                          ContraEnv Γ →
                          Γ ⊢ U <: U′
  upper-bound-extract drefl all        = drefl
  upper-bound-extract (dbnd D₁ D₂) all = D₂

  ub-extract-measure : ∀ {Γ S S′ U U′}
                         (D : Γ ⊢ ⟨A: S ⋯ U ⟩ <: ⟨A: S′ ⋯ U′ ⟩)
                         (all : ContraEnv Γ) →
                         D-measure D ≥ D-measure (upper-bound-extract D all)
  ub-extract-measure drefl all        = s≤s z≤n
  ub-extract-measure (dbnd D₁ D₂) all = ≤-step $ ≤-stepsˡ _ ≤-refl

  ⟨A:⊥⟩<:-lb : ∀ {Γ T S U} → Γ ⊢ ⟨A: ⊥ ⋯ T ⟩ <: ⟨A: S ⋯ U ⟩ → ContraEnv Γ → S ≡ ⊥
  ⟨A:⊥⟩<:-lb D cΓ with ⟨A:⟩<:⟨A:⟩ (D⇒Dᵢ D cΓ) cΓ
  ... | S<:⊥ , _  with <:⊥ S<:⊥ cΓ
  ...                | S≡⊥ = S≡⊥

  ∙A<:! : ∀ {Γ n T} → (D : Γ ⊢ n ∙A <: T) → ContraEnv Γ →
            T ≡ ⊤ ⊎
            T ≡ n ∙A ⊎
            ∃ (λ T′ → env-lookup Γ n ≡ just ⟨A: ⊥ ⋯ T′ ⟩ ×
                      Σ (Γ ⊢ T′ <: T) λ { D′ → D-measure D > D-measure D′ })
  ∙A<:! dtop cΓ  = inj₁ refl
  ∙A<:! drefl cΓ = inj₂ (inj₁ refl)
  ∙A<:! (dsel₁ T∈Γ D) cΓ with lookupContraEnv T∈Γ cΓ
  ... | ctt _ with ⟨A:⊥⟩<:-lb D cΓ
  ...            | ()
  ∙A<:! (dsel₂ T∈Γ D) cΓ with lookupContraEnv T∈Γ cΓ
  ... | ctt _    = inj₂ (inj₂ (-, T∈Γ , upper-bound-extract D cΓ
                                      , s≤s (ub-extract-measure D cΓ)))

  module _ where
    private
      prop : Env → Typ → Typ → Set
      prop Γ S U = ContraEnv Γ → Covar S → Covar U → Γ ⊢ᵣ S <: U

      prop-pack : D-deriv → Set
      prop-pack D = ContraEnv (env D) → Covar (typ₁ D) → Covar (typ₂ D) → env D ⊢ᵣ typ₁ D <: typ₂ D

    D<:⇒D<:ᵣ-gen : ∀ {Γ S U} (S<:U : Γ ⊢ S <: U) →
                     (∀ {Γ′ S′ U′} (S′<:U′ : Γ′ ⊢ S′ <: U′) →
                        D-measure S′<:U′ < D-measure S<:U →
                        prop Γ′ S′ U′) →
                     prop Γ S U
    D<:⇒D<:ᵣ-gen dtop rec cΓ S U       = drtop S
    D<:⇒D<:ᵣ-gen dbot rec cΓ () U
    D<:⇒D<:ᵣ-gen drefl rec cΓ S U      = drrefl U
    D<:⇒D<:ᵣ-gen (dbnd S′<:S U<:U′) rec cΓ () U
    D<:⇒D<:ᵣ-gen (dall S′<:S U<:U′) rec cΓ (cvΠ S U) (cvΠ S′ U′)
      with upper-bound-extract S′<:S cΓ | ub-extract-measure S′<:S cΓ
    ... | <: | measure≤                = drall S U S′ U′
                                          (rec <: (s≤s (≤-stepsʳ _ measure≤)) cΓ S′ S)
                                          (D<:⇒D<:ᵣ-gen U<:U′ (λ <: measure< → rec <: (≤-step (≤-stepsˡ _ measure<)))
                                                        (ctt S′ ∷ cΓ) U U′)
    D<:⇒D<:ᵣ-gen (dsel₁ T∈Γ T<:⟨SU⟩) rec cΓ S U with lookupContraEnv T∈Γ cΓ
    ... | ctt _ with ⟨A:⊥⟩<:-lb T<:⟨SU⟩ cΓ
    ...            | refl with S
    ...                      | ()
    D<:⇒D<:ᵣ-gen (dsel₂ T∈Γ T<:⟨SU⟩) rec cΓ S U with lookupContraEnv T∈Γ cΓ
    ... | ctt T′ with upper-bound-extract T<:⟨SU⟩ cΓ | ub-extract-measure T<:⟨SU⟩ cΓ
    ...             | T′<:U | measure≤ = drsel T∈Γ T′ (rec T′<:U (s≤s measure≤) cΓ T′ U)

    D<:⇒D<:ᵣ : ∀ {Γ S U} → Γ ⊢ S <: U → prop Γ S U
    D<:⇒D<:ᵣ D cΓ S U = aux (-, D) cΓ S U
      where open Measure <-wellFounded D-measure-pack
            aux : ∀ D → prop-pack D
            aux = wfRec prop-pack
                        λ { (_ , D) rec →
                          D<:⇒D<:ᵣ-gen D λ D′ measure< → rec (-, D′) measure< }

  D<:ᵣ⇒D<: : ∀ {Γ S U} → Γ ⊢ᵣ S <: U → Γ ⊢ S <: U
  D<:ᵣ⇒D<: (drtop x)                   = dtop
  D<:ᵣ⇒D<: (drrefl x)                  = drefl
  D<:ᵣ⇒D<: (drall _ _ _ _ S′<:S U<:U′) = dall (dbnd dbot (D<:ᵣ⇒D<: S′<:S)) (D<:ᵣ⇒D<: U<:U′)
  D<:ᵣ⇒D<: (drsel T∈Γ _ S<:U)          = dsel₂ T∈Γ (dbnd dbot (D<:ᵣ⇒D<: S<:U))


  open FsubMinus.FsubMinus

  F<:⇒D<: : ∀ {Γ S U} → Γ ⊢F S <: U → ⟪ Γ ⟫ ⊢ ⟦ S ⟧ <: ⟦ U ⟧
  F<:⇒D<: = D<:ᵣ⇒D<: ∘ F<:⇒D<:ᵣ

  D<:⇒F<: : ∀ {Γ S U} → ⟪ Γ ⟫ ⊢ ⟦ S ⟧ <: ⟦ U ⟧ → Γ ⊢F S <: U
  D<:⇒F<: S<:U = D<:ᵣ⇒F<: (D<:⇒D<:ᵣ S<:U (⟪⟫-contraEnv _) (⟦⟧-covar _) (⟦⟧-covar _))
                          refl refl refl
