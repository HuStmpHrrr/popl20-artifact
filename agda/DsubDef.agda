{-# OPTIONS --without-K --safe #-}

-- In this module, we define the syntax of D<:
module DsubDef where

open import Data.List as List
open import Data.List.All
open import Data.Nat as ℕ
open import Data.Maybe as Maybe
open import Data.Product
open import Data.Sum
open import Data.Empty renaming (⊥ to False)
open import Function

open import Data.Nat.Properties as ℕₚ
open import Data.Maybe.Properties as Maybeₚ
open import Relation.Nullary
open import Relation.Binary.PropositionalEquality

open import Utils

infix 8 _∙A
infix 6 Π_∙_ ⟨A:_⋯_⟩

-- Types
--
-- Notations in Agda should be more readable than in Coq.
-- * ⊤ is a supertype of all types.
-- * ⊥ is a subtype of all types.
-- * (x ∙A) represents a path dependent type (x.A).
-- * (Π S ∙ U) represents a dependent function type (∀(x : S)U).
-- * (⟨A: S ⋯ U ⟩) represents a type declaration ({A : S .. U}).
data Typ : Set where
  ⊤       : Typ
  ⊥       : Typ
  _∙A     : (n : ℕ) → Typ
  Π_∙_    : (S U : Typ) → Typ
  ⟨A:_⋯_⟩ : (S U : Typ) → Typ

-- typing context
Env : Set
Env = List Typ

-- shifting operation of de Bruijn indices
infixl 7 _↑_
_↑_ : Typ → ℕ → Typ
⊤ ↑ n           = ⊤
⊥ ↑ n           = ⊥
(x ∙A) ↑ n with n ≤? x
... | yes n≤x   = suc x ∙A
... | no n>x    = x ∙A
(Π S ∙ U) ↑ n   = Π S ↑ n ∙ U ↑ suc n
⟨A: S ⋯ U ⟩ ↑ n = ⟨A: S ↑ n ⋯ U ↑ n ⟩

-- The remaining are technical setup.
infix 4 _↦_∈_
data _↦_∈_ : ℕ → Typ → Env → Set where
  hd : ∀ {T Γ} → 0 ↦ T ↑ 0 ∈ T ∷ Γ
  tl : ∀ {n T T′ Γ} → n ↦ T ∈ Γ → suc n ↦ T ↑ 0 ∈ T′ ∷ Γ

env-lookup : Env → ℕ → Maybe Typ
env-lookup Γ n = Maybe.map (repeat (suc n) (_↑ 0)) (lookupOpt Γ n)

↦∈⇒lookup : ∀ {x T Γ} → x ↦ T ∈ Γ → env-lookup Γ x ≡ just T
↦∈⇒lookup hd = refl
↦∈⇒lookup {x} {_} {Γ} (tl T∈Γ) with lookupOpt Γ x | ↦∈⇒lookup T∈Γ
... | just T′ | eq = cong (just ∘ (_↑ zero)) (just-injective eq)
... | nothing | ()

lookup⇒↦∈ : ∀ {x T Γ} → env-lookup Γ x ≡ just T → x ↦ T ∈ Γ
lookup⇒↦∈ {x} {_} {[]} ()
lookup⇒↦∈ {zero} {_} {T ∷ Γ} refl = hd
lookup⇒↦∈ {suc x} {_} {T ∷ Γ} eq with lookupOpt Γ x | λ {T} → lookup⇒↦∈ {x} {T} {Γ}
lookup⇒↦∈ refl | just T′ | rec = tl $ rec refl
lookup⇒↦∈ ()   | nothing | _

⟨A:⟩-injective : ∀ {S U S′ U′} → ⟨A: S ⋯ U ⟩ ≡ ⟨A: S′ ⋯ U′ ⟩ → S ≡ S′ × U ≡ U′
⟨A:⟩-injective refl = refl , refl

↑-idx : ℕ → ℕ → ℕ
↑-idx x n with n ≤? x
... | yes p = suc x
... | no ¬p = x

↑-var : ∀ x n → x ∙A ↑ n ≡ ↑-idx x n ∙A
↑-var x n with n ≤? x
... | yes p = refl
... | no ¬p = refl

↑-↑-comm : ∀ T m n → m ≤ n → T ↑ m ↑ suc n ≡ T ↑ n ↑ m
↑-↑-comm ⊤ m n m≤n                                  = refl
↑-↑-comm ⊥ m n m≤n                                  = refl
↑-↑-comm (x ∙A) m n m≤n with n ≤? x
... | yes n≤x
    rewrite ≤?-yes (≤-trans m≤n n≤x)
          | ≤?-yes n≤x
          | ≤?-yes (≤-step (≤-trans m≤n n≤x))       = refl
... | no n>x with m ≤? x
...             | yes m≤x rewrite proj₂ $ ≤?-no n>x = refl
...             | no m>x with suc n ≤? x
...                         | yes 1+n≤x             = ⊥-elim (m>x (≤-trans (≤-step m≤n) 1+n≤x))
...                         | no 1+n>x              = refl
↑-↑-comm (Π S ∙ U) m n m≤n
  rewrite ↑-↑-comm S m n m≤n
        | ↑-↑-comm U (suc m) (suc n) (s≤s m≤n)      = refl
↑-↑-comm ⟨A: S ⋯ U ⟩ m n m≤n
  rewrite ↑-↑-comm S m n m≤n | ↑-↑-comm U m n m≤n   = refl

-- These two judgments are about to capture the characteristics of the image of
-- interpretation functions from F<:⁻ to D<:.
--
-- Covar quantifies the types in D<: which appears in the covariant positions in the
-- image of the interpretation function.
data Covar : Typ → Set where
  cv⊤  : Covar ⊤
  cv∙A : ∀ n → Covar (n ∙A)
  cvΠ  : ∀ {S U} → Covar S → Covar U → Covar (Π ⟨A: ⊥ ⋯ S ⟩ ∙ U)

-- Contra quantifies the types in D<: which appears in the contravariant positions in
-- the image of the interpretation function.
data Contra : Typ → Set where
  ctt : ∀ {T} → Covar T → Contra ⟨A: ⊥ ⋯ T ⟩

ContraEnv : Env → Set
ContraEnv = All Contra

↑-Covar : ∀ {T} n → Covar T → Covar (T ↑ n)
↑-Covar n cv⊤       = cv⊤
↑-Covar n (cv∙A x)
  rewrite ↑-var x n = cv∙A _
↑-Covar n (cvΠ S U) = cvΠ (↑-Covar n S) (↑-Covar (suc n) U)

↑-Contra : ∀ {T} n → Contra T → Contra (T ↑ n)
↑-Contra n (ctt T) = ctt (↑-Covar n T)

↑-injective : ∀ {S U n} → S ↑ n ≡ U ↑ n → S ≡ U
↑-injective {⊤} {⊤} {n} eq = refl
↑-injective {⊤} {⊥} {n} ()
↑-injective {⊤} {x ∙A} {n} eq
  rewrite ↑-var x n        = case eq of λ ()
↑-injective {⊤} {Π S ∙ U} {n} ()
↑-injective {⊤} {⟨A: S ⋯ U ⟩} {n} ()
↑-injective {⊥} {⊤} {n} ()
↑-injective {⊥} {⊥} {n} eq = refl
↑-injective {⊥} {x ∙A} {n} eq
  rewrite ↑-var x n        = case eq of λ ()
↑-injective {⊥} {Π S ∙ U} {n} ()
↑-injective {⊥} {⟨A: S ⋯ U ⟩} {n} ()
↑-injective {x ∙A} {⊤} {n} eq
  rewrite ↑-var x n        = case eq of λ ()
↑-injective {x ∙A} {⊥} {n} eq
  rewrite ↑-var x n        = case eq of λ ()
↑-injective {x ∙A} {y ∙A} {n} eq
  with n ≤? x | n ≤? y
↑-injective {x ∙A} {y ∙A} {n} refl
    | yes n≤x | yes n≤y    = refl
↑-injective {x ∙A} {y ∙A} {n} refl
    | yes n≤x | no n>y     = ⊥-elim (n>y (≤-step n≤x))
↑-injective {x ∙A} {y ∙A} {n} refl
    | no n>x  | yes n≤y    = ⊥-elim (n>x (≤-step n≤y))
↑-injective {x ∙A} {y ∙A} {n} refl
    | no n>x  | no n>y     = refl
↑-injective {x ∙A} {Π S ∙ U} {n} eq
  rewrite ↑-var x n        = case eq of λ ()
↑-injective {x ∙A} {⟨A: S ⋯ U ⟩} {n} eq
  rewrite ↑-var x n        = case eq of λ ()
↑-injective {Π S ∙ U} {⊤} {n} ()
↑-injective {Π S ∙ U} {⊥} {n} ()
↑-injective {Π S ∙ U} {x ∙A} {n} eq
  rewrite ↑-var x n        = case eq of λ ()
↑-injective {Π S ∙ U} {Π S′ ∙ U′} {n} eq
  with S ↑ n | U ↑ suc n | S′ ↑ n | U′ ↑ suc n
     | ↑-injective {S} {S′} {n} | ↑-injective {U} {U′} {suc n}
...  | _ | _ | _ | _ | rec₁ | rec₂
     with eq
...     | refl             = cong₂ Π_∙_ (rec₁ refl) (rec₂ refl)
↑-injective {Π S ∙ U} {⟨A: _ ⋯ _ ⟩} {n} ()
↑-injective {⟨A: S ⋯ U ⟩} {⊤} {n} ()
↑-injective {⟨A: S ⋯ U ⟩} {⊥} {n} ()
↑-injective {⟨A: S ⋯ U ⟩} {x ∙A} {n} eq
  rewrite ↑-var x n        = case eq of λ ()
↑-injective {⟨A: S ⋯ U ⟩} {Π _ ∙ _} {n} ()
↑-injective {⟨A: S ⋯ U ⟩} {⟨A: S′ ⋯ U′ ⟩} {n} eq
  with S ↑ n | U ↑ n | S′ ↑ n | U′ ↑ n
     | ↑-injective {S} {S′} {n} | ↑-injective {U} {U′} {n}
...  | _ | _ | _ | _ | rec₁ | rec₂
     with eq
...     | refl             = cong₂ ⟨A:_⋯_⟩ (rec₁ refl) (rec₂ refl)

↑-⊥-inv : ∀ {S n} → S ↑ n ≡ ⊥ → S ≡ ⊥
↑-⊥-inv {⊤} {n} ()
↑-⊥-inv {⊥} {n} refl = refl
↑-⊥-inv {x ∙A} {n} eq
  rewrite ↑-var x n  = case eq of λ ()
↑-⊥-inv {Π _ ∙ _} {n} ()
↑-⊥-inv {⟨A: _ ⋯ _ ⟩} {n} ()

⟨A:⟩-↑-inv : ∀ {T n S U} → ⟨A: S ⋯ U ⟩ ≡ T ↑ n → ∃₂ λ S′ U′ → T ≡ ⟨A: S′ ⋯ U′ ⟩ × S ≡ S′ ↑ n × U ≡ U′ ↑ n
⟨A:⟩-↑-inv {⊤} ()
⟨A:⟩-↑-inv {⊥} ()
⟨A:⟩-↑-inv {x ∙A} {n} eq
  rewrite ↑-var x n             = case eq of λ ()
⟨A:⟩-↑-inv {Π _ ∙ _} ()
⟨A:⟩-↑-inv {⟨A: S′ ⋯ U′ ⟩} refl = S′ , U′ , refl , refl , refl

↦∈ContraEnv : ∀ {Γ n T} → n ↦ T ∈ Γ → ContraEnv Γ → Contra T
↦∈ContraEnv hd (T ∷ cT)       = ↑-Contra 0 T
↦∈ContraEnv (tl T∈Γ) (_ ∷ cT) = ↑-Contra 0 (↦∈ContraEnv T∈Γ cT)

lookupContraEnv : ∀ {Γ n T} → env-lookup Γ n ≡ just T → ContraEnv Γ → Contra T
lookupContraEnv lk cT = ↦∈ContraEnv (lookup⇒↦∈ lk) cT

lookupContraBot : ∀ {Γ n} → ContraEnv Γ → ¬ env-lookup Γ n ≡ just ⊥
lookupContraBot all eq with lookupContraEnv eq all
... | ()

lookupContraBndBot : ∀ {Γ n S} → ContraEnv Γ → ¬ env-lookup Γ n ≡ just ⟨A: S ⋯ ⊥ ⟩
lookupContraBndBot all eq with lookupContraEnv eq all
... | ctt ()

lookupContraBndBnd : ∀ {Γ n T S U} → ContraEnv Γ →
                       ¬ env-lookup Γ n ≡ just ⟨A: T ⋯ ⟨A: S ⋯ U ⟩ ⟩
lookupContraBndBnd all eq with lookupContraEnv eq all
... | ctt ()

lookupContra⊥Lb : ∀ {Γ n S U} → ContraEnv Γ →
                    env-lookup Γ n ≡ just ⟨A: S ⋯ U ⟩ → S ≡ ⊥
lookupContra⊥Lb all eq with lookupContraEnv eq all
... | ctt _ = refl

Typ-measure : Typ → ℕ
Typ-measure ⊤           = 1
Typ-measure ⊥           = 1
Typ-measure (_ ∙A)      = 2
Typ-measure (Π S ∙ U)   = 1 + Typ-measure S + Typ-measure U
Typ-measure ⟨A: S ⋯ U ⟩ = 1 + Typ-measure S + Typ-measure U

Typ-measure-↑ : ∀ T n → Typ-measure (T ↑ n) ≡ Typ-measure T
Typ-measure-↑ ⊤ n                 = refl
Typ-measure-↑ ⊥ n                 = refl
Typ-measure-↑ (x ∙A) n
  rewrite ↑-var x n               = refl
Typ-measure-↑ (Π S ∙ U) n
  rewrite Typ-measure-↑ S n
        | Typ-measure-↑ U (suc n) = refl
Typ-measure-↑ ⟨A: S ⋯ U ⟩ n
  rewrite Typ-measure-↑ S n
        | Typ-measure-↑ U n       = refl

-- Definition of Invertible Contexts
--
-- As per Definition 9, we define a predicate for invertible contexts.
record InvertibleEnv (P : Env → Set) : Set where
  field
    no-⊥       : ∀ {Γ n} → P Γ → ¬ env-lookup Γ n ≡ just ⊥
    no-bnd-⊥   : ∀ {Γ n S} → P Γ → ¬ env-lookup Γ n ≡ just ⟨A: S ⋯ ⊥ ⟩
    no-bnd-bnd : ∀ {Γ n T S U} → P Γ → ¬ env-lookup Γ n ≡ just ⟨A: T ⋯ ⟨A: S ⋯ U ⟩ ⟩
    ⊥-lb       : ∀ {Γ n S U} → P Γ → env-lookup Γ n ≡ just ⟨A: S ⋯ U ⟩ → S ≡ ⊥

contraInvertible : InvertibleEnv ContraEnv
contraInvertible = record
  { no-⊥       = lookupContraBot
  ; no-bnd-⊥   = lookupContraBndBot
  ; no-bnd-bnd = lookupContraBndBnd
  ; ⊥-lb       = lookupContra⊥Lb
  }

-- Properties of Invertible Contexts
--
-- Just by knowing the contexts being invertible, we can already derive many
-- properties of D<:. In the following module, we show that in invertible contexts,
-- inversion properties are recovered. For technical reasons, we leave the subtyping
-- judgment open in order to accomodate multiple definition of subtyping in D<:.
-- These properties are discussed in Section 4.4.
module InvertibleProperties {P : Env → Set}
                            (invertible : InvertibleEnv P)
                            (_⊢_<:_ : Env → Typ → Typ → Set) where
  open InvertibleEnv invertible public
  
  infix 4 _⊢ᵢ_<:_
  data _⊢ᵢ_<:_ : Env → Typ → Typ → Set where
    ditop   : ∀ {Γ T} → Γ ⊢ᵢ T <: ⊤
    dibot   : ∀ {Γ T} → Γ ⊢ᵢ ⊥ <: T
    direfl  : ∀ {Γ T} → Γ ⊢ᵢ T <: T
    ditrans : ∀ {Γ S U} T →
                (S<:T : Γ ⊢ᵢ S <: T) →
                (T<:U : Γ ⊢ᵢ T <: U) →
                Γ ⊢ᵢ S <: U
    dibnd   : ∀ {Γ S U S′ U′} →
                (S′<:S : Γ ⊢ᵢ S′ <: S) →
                (U<:U′ : Γ ⊢ᵢ U <: U′) →
                Γ ⊢ᵢ ⟨A: S ⋯ U ⟩ <: ⟨A: S′ ⋯ U′ ⟩
    diall   : ∀ {Γ S U S′ U′} →
                (S′<:S : Γ ⊢ᵢ S′ <: S) →
                (U<:U′ : (Γ ‣ S′ !) ⊢ U <: U′) →
                Γ ⊢ᵢ Π S ∙ U <: Π S′ ∙ U′
    disel   : ∀ {Γ n U} →
                (T∈Γ : env-lookup Γ n ≡ just ⟨A: ⊥ ⋯ U ⟩) →
                Γ ⊢ᵢ n ∙A <: U

  module _ where
    
    ⊤<: : ∀ {Γ T} → Γ ⊢ᵢ ⊤ <: T → T ≡ ⊤
    ⊤<: ditop  = refl
    ⊤<: direfl = refl
    ⊤<: (ditrans T S<:T T<:U) with ⊤<: S<:T
    ... | refl = ⊤<: T<:U

    <:⊥ : ∀ {Γ T} → Γ ⊢ᵢ T <: ⊥ → P Γ → T ≡ ⊥
    <:⊥ dibot pΓ       = refl
    <:⊥ direfl pΓ      = refl
    <:⊥ (ditrans T S<:T T<:U) pΓ with <:⊥ T<:U pΓ
    ... | refl         = <:⊥ S<:T pΓ
    <:⊥ (disel T∈Γ) pΓ = ⊥-elim (no-bnd-⊥ pΓ T∈Γ)

    ⟨A:⟩<: : ∀ {Γ T S U} → Γ ⊢ᵢ ⟨A: S ⋯ U ⟩ <: T → T ≡ ⊤ ⊎ ∃₂ (λ S′ U′ → T ≡ ⟨A: S′ ⋯ U′ ⟩)
    ⟨A:⟩<: ditop            = inj₁ refl
    ⟨A:⟩<: direfl           = inj₂ (-, -, refl)
    ⟨A:⟩<: (ditrans T S<:T T<:U) with ⟨A:⟩<: S<:T
    ... | inj₁ refl         = inj₁ (⊤<: T<:U)
    ... | inj₂ (_ , _ , refl) with ⟨A:⟩<: T<:U
    ... | inj₁ eq           = inj₁ eq
    ... | inj₂ (_ , _ , eq) = inj₂ (-, -, eq)
    ⟨A:⟩<: (dibnd D₁ D₂)    = inj₂ (-, -, refl)

    <:⟨A:⟩ : ∀ {Γ T S U} → Γ ⊢ᵢ T <: ⟨A: S ⋯ U ⟩ → P Γ →
               T ≡ ⊥ ⊎ ∃₂ (λ S′ U′ → T ≡ ⟨A: S′ ⋯ U′ ⟩)
    <:⟨A:⟩ dibot pΓ           = inj₁ refl
    <:⟨A:⟩ direfl pΓ          = inj₂ (-, -, refl)
    <:⟨A:⟩ (ditrans T S<:T T<:U) pΓ with <:⟨A:⟩ T<:U pΓ
    ... | inj₁ refl           = inj₁ (<:⊥ S<:T pΓ)
    ... | inj₂ (S′ , U′ , refl) with <:⟨A:⟩ S<:T pΓ
    ... | inj₁ eq             = inj₁ eq
    ... | inj₂ (S″ , U″ , eq) = inj₂ (S″ , U″ , eq)
    <:⟨A:⟩ (dibnd D₁ D₂) pΓ   = inj₂ (-, -, refl)
    <:⟨A:⟩ (disel T∈Γ) pΓ     = ⊥-elim (no-bnd-bnd pΓ T∈Γ)

    ⟨A:⟩<:⟨A:⟩ : ∀ {Γ S S′ U U′} → Γ ⊢ᵢ ⟨A: S ⋯ U ⟩ <: ⟨A: S′ ⋯ U′ ⟩ → P Γ →
                   Γ ⊢ᵢ S′ <: S × Γ ⊢ᵢ U <: U′
    ⟨A:⟩<:⟨A:⟩ direfl pΓ                  = direfl , direfl
    ⟨A:⟩<:⟨A:⟩ (ditrans T S<:T T<:U) pΓ with ⟨A:⟩<: S<:T
    ... | inj₁ refl with ⊤<: T<:U
    ... | ()
    ⟨A:⟩<:⟨A:⟩ (ditrans T S<:T T<:U) pΓ | inj₂ (_ , _ , refl)
      with ⟨A:⟩<:⟨A:⟩ S<:T pΓ | ⟨A:⟩<:⟨A:⟩ T<:U pΓ
    ... | S″<:S , U<:U″ | S′<:S″ , U″<:U′ = ditrans _ S′<:S″ S″<:S , ditrans _ U<:U″ U″<:U′
    ⟨A:⟩<:⟨A:⟩ (dibnd D₁ D₂) pΓ           = D₁ , D₂

    infix 4 _reach_from_
    data _reach_from_ : Env → Typ → ℕ → Set where
      /_/ : ∀ {Γ n T} →
              env-lookup Γ n ≡ just ⟨A: ⊥ ⋯ T ⟩ →
              Γ reach T from n
      _∷_ : ∀ {Γ n m T} →
              env-lookup Γ n ≡ just ⟨A: ⊥ ⋯ m ∙A ⟩ →
              Γ reach T from m →
              Γ reach T from n
      
    rf-concat : ∀ {Γ T m n} → Γ reach T from m → Γ reach m ∙A from n → Γ reach T from n
    rf-concat m↝T / B∈Γ /       = B∈Γ ∷ m↝T
    rf-concat m↝T (B∈Γ ∷ n↝m∙A) = B∈Γ ∷ rf-concat m↝T n↝m∙A

    ∙A<: : ∀ {Γ n T} → Γ ⊢ᵢ n ∙A <: T →
             T ≡ ⊤ ⊎ T ≡ n ∙A ⊎ ∃ λ T′ → Γ reach T′ from n × Γ ⊢ᵢ T′ <: T
    ∙A<: ditop                            = inj₁ refl
    ∙A<: direfl                           = inj₂ (inj₁ refl)
    ∙A<: (ditrans T S<:T T<:U) with ∙A<: S<:T
    ... | inj₁ refl                       = inj₁ (⊤<: T<:U)
    ... | inj₂ (inj₁ refl)                = ∙A<: T<:U
    ... | inj₂ (inj₂ (T′ , n↝T′ , T′<:T)) = inj₂ (inj₂ (T′ , n↝T′ , ditrans _ T′<:T T<:U))
    ∙A<: (disel T∈Γ)                      = inj₂ (inj₂ (-, / T∈Γ / , direfl))

    <:∙A : ∀ {Γ n T} → Γ ⊢ᵢ T <: n ∙A → P Γ →
             T ≡ ⊥ ⊎
             T ≡ n ∙A ⊎
             ∃ (λ m → T ≡ m ∙A × Γ reach n ∙A from m)
    <:∙A dibot pΓ                             = inj₁ refl
    <:∙A direfl pΓ                            = inj₂ (inj₁ refl)
    <:∙A (ditrans T S<:T T<:U) pΓ with <:∙A T<:U pΓ
    ... | inj₁ refl                           = inj₁ (<:⊥ S<:T pΓ)
    ... | inj₂ (inj₁ refl)                    = <:∙A S<:T pΓ
    ... | inj₂ (inj₂ (m , refl , m↝n∙A))
        with <:∙A S<:T pΓ
    ...    | inj₁ refl                        = inj₁ refl
    ...    | inj₂ (inj₁ refl)                 = inj₂ (inj₂ (-, refl , m↝n∙A))
    ...    | inj₂ (inj₂ (m′ , refl , m′↝m∙A)) = inj₂ (inj₂ (-, refl , rf-concat m↝n∙A m′↝m∙A))
    <:∙A (disel T∈Γ) pΓ                       = inj₂ (inj₂ (-, refl , / T∈Γ /))

    Π<: : ∀ {Γ S U T} → Γ ⊢ᵢ Π S ∙ U <: T →
            T ≡ ⊤ ⊎ ∃₂ (λ S′ U′ → T ≡ Π S′ ∙ U′)
    Π<: ditop                 = inj₁ refl
    Π<: direfl                = inj₂ (-, -, refl)
    Π<: (ditrans T S<:T T<:U) with Π<: S<:T
    ... | inj₁ refl           = inj₁ (⊤<: T<:U)
    ... | inj₂ (_ , _ , refl) = Π<: T<:U
    Π<: (diall D₁ D₂)         = inj₂ (-, -, refl)

    <:Π : ∀ {Γ S U T} → Γ ⊢ᵢ T <: Π S ∙ U → P Γ →
            T ≡ ⊥ ⊎
            ∃ (λ n → T ≡ n ∙A) ⊎
            ∃₂ (λ S′ U′ → T ≡ Π S′ ∙ U′)
    <:Π dibot pΓ                       = inj₁ refl
    <:Π direfl pΓ                      = inj₂ (inj₂ (-, -, refl))
    <:Π (ditrans T S<:T T<:U) pΓ with <:Π T<:U pΓ
    ... | inj₁ refl                    = inj₁ (<:⊥ S<:T pΓ)
    ... | inj₂ (inj₁ (_ , refl)) with <:∙A S<:T pΓ
    ... | inj₁ eq                      = inj₁ eq
    ... | inj₂ (inj₁ eq)               = inj₂ (inj₁ (-, eq))
    ... | inj₂ (inj₂ (_ , eq , _))     = inj₂ (inj₁ (-, eq))
    <:Π (ditrans T S<:T T<:U) pΓ | inj₂ (inj₂ (_ , _ , refl))
                                       = <:Π S<:T pΓ
    <:Π (diall D₁ D₂) pΓ               = inj₂ (inj₂ (-, -, refl))
    <:Π (disel T∈Γ) pΓ                 = inj₂ (inj₁ (-, refl))

    Π<:Π : ∀ {Γ S U S′ U′} →
             Γ ⊢ᵢ Π S ∙ U <: Π S′ ∙ U′ →
             P Γ →
             Γ ⊢ᵢ S′ <: S
    Π<:Π direfl pΓ                = direfl
    Π<:Π (ditrans T Π<:T T<:Π′) pΓ with Π<: Π<:T
    ... | inj₁ refl               = case ⊤<: T<:Π′ of λ ()
    ... | inj₂ (_ , _ , refl)
        with Π<:Π Π<:T pΓ | Π<:Π T<:Π′ pΓ
    ...    | S″<:S        | S′<:S = ditrans _ S′<:S S″<:S
    Π<:Π (diall Π<:Π′ U<:U′) pΓ   = Π<:Π′

-- Terms and Values
infix 6 var_ val_
infix 6 ⟨A=_⟩ _$$_
infixr 7 lt_inn_
infixr 6 Λ_∙_

mutual
  -- Values
  --
  -- * (⟨A= T ⟩) represents a type tag ({A = T}).
  -- * (Λ T ∙ t) represents a lambda expression (λ(x : T)t)
  data Val : Set where
    ⟨A=_⟩  : (T : Typ) → Val
    Λ_∙_   : (T : Typ) → (t : Trm) → Val

  -- Terms
  --
  -- * (var x) represents a variable.
  -- * (val v) represents a value as a term.
  -- * (x $$ y) is an application of two variables.
  -- * (lt t inn u) represents let binding (let x = t in u).
  data Trm  : Set where
    var_    : ℕ → Trm
    val_    : (v : Val) → Trm
    _$$_    : (x y : ℕ) → Trm
    lt_inn_ : Trm → Trm → Trm

-- substitution operation
record Subst (T : Set) : Set where
  infixl 5 _[_/_]
  field
    _[_/_] : T → ℕ → ℕ → T

open Subst {{...}} public

infixl 5 _[_/_]ᵥ _[_/_]ₜ _[_/_]T

ℕsubst : ℕ → ℕ → ℕ → ℕ
ℕsubst x n m with x ≟ m
... | yes x≡m = n
... | no x≢m  = x

instance
  substℕ : Subst ℕ
  substℕ = record { _[_/_] = ℕsubst }

_[_/_]T : Typ → ℕ → ℕ → Typ
⊤ [ n / m ]T           = ⊤
⊥ [ n / m ]T           = ⊥
x ∙A [ n / m ]T        = (x [ n / m ]) ∙A
Π S ∙ U [ n / m ]T     = Π S [ n / m ]T ∙ (U [ suc n / suc m ]T)
⟨A: S ⋯ U ⟩ [ n / m ]T = ⟨A: S [ n / m ]T ⋯ U [ n / m ]T ⟩

instance
  substTyp : Subst Typ
  substTyp = record { _[_/_] = _[_/_]T }

mutual
  _[_/_]ᵥ : Val → ℕ → ℕ → Val
  ⟨A= T ⟩ [ n / m ]ᵥ = ⟨A= T [ n / m ] ⟩
  Λ T ∙ t [ n / m ]ᵥ = Λ T [ n / m ] ∙ (t [ suc n / suc m ]ₜ)

  _[_/_]ₜ : Trm → ℕ → ℕ → Trm
  var x [ n / m ]ₜ      = var (x [ n / m ])
  val v [ n / m ]ₜ      = val (v [ n / m ]ᵥ)
  x $$ y [ n / m ]ₜ     = (x [ n / m ]) $$ (y [ n / m ])
  lt t inn u [ n / m ]ₜ = lt (t [ n / m ]ₜ) inn (u [ suc n / suc m ]ₜ)

instance
  substVal : Subst Val
  substVal = record { _[_/_] = _[_/_]ᵥ }

  substTrm : Subst Trm
  substTrm = record { _[_/_] = _[_/_]ₜ }

data Closed : ℕ → Typ → Set where
  cl-⊤   : ∀ {n} → Closed n ⊤
  cl-⊥   : ∀ {n} → Closed n ⊥
  cl-∙A  : ∀ {n m} (m≥n : m ≥ n) → Closed n (m ∙A)
  cl-Π   : ∀ {n S U} → Closed n S → Closed (suc n) U → Closed n (Π S ∙ U)
  cl-⟨A⟩ : ∀ {n S U} → Closed n S → Closed n U → Closed n ⟨A: S ⋯ U ⟩

infix 7 _↓
_↓ : ∀ {n T} → Closed (suc n) T → Typ
cl-⊤ ↓              = ⊤
cl-⊥ ↓              = ⊥
cl-∙A {_} {m} m≥n ↓ = pred m ∙A
cl-Π S U ↓          = Π S ↓ ∙ (U ↓)
cl-⟨A⟩ S U ↓        = ⟨A: S ↓ ⋯ U ↓ ⟩
