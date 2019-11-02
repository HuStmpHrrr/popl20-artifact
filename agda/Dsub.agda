{-# OPTIONS --without-K --safe #-}

-- In this module, we define the subtyping relation of D<: according to Lemma 2.
module Dsub where

open import Data.List as List
open import Data.List.All as All
open import Data.Nat as ℕ
open import Data.Maybe as Maybe
open import Data.Product as Σ
open import Data.Sum
open import Data.Empty renaming (⊥ to False)
open import Data.Vec as Vec renaming (_∷_ to _‼_ ; [] to nil) hiding (_++_)
open import Function

open import Data.Maybe.Properties as Maybeₚ
open import Data.Nat.Properties as ℕₚ
open import Relation.Nullary
open import Relation.Binary.PropositionalEquality

open import DsubDef
open import Utils

module Dsub where

  infix 4 _⊢_<:_

  data _⊢_<:_ : Env → Typ → Typ → Set where
    dtop   : ∀ {Γ T} →
      Γ ⊢ T <: ⊤
    dbot   : ∀ {Γ T} →
      Γ ⊢ ⊥ <: T
    drefl  : ∀ {Γ T} →
      Γ ⊢ T <: T
    dtrans : ∀ {Γ S U} T →
      (S<:T : Γ ⊢ S <: T) →
      (T<:U : Γ ⊢ T <: U) →
      Γ ⊢ S <: U
    dbnd   : ∀ {Γ S U S′ U′} →
      (S′<:S : Γ ⊢ S′ <: S) →
      (U<:U′ : Γ ⊢ U <: U′) →
      Γ ⊢ ⟨A: S ⋯ U ⟩ <: ⟨A: S′ ⋯ U′ ⟩
    dall   : ∀ {Γ S U S′ U′} →
      (S′<:S : Γ ⊢ S′ <: S) →
      (U<:U′ : (S′ ∷ Γ) ⊢ U <: U′) →
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
  D-measure dtop                 = 1
  D-measure dbot                 = 1
  D-measure drefl                = 1
  D-measure (dtrans _ S<:T T<:U) = 1 + D-measure S<:T + D-measure T<:U
  D-measure (dbnd D₁ D₂)         = 1 + D-measure D₁ + D-measure D₂
  D-measure (dall Dp Db)         = 1 + D-measure Dp + D-measure Db
  D-measure (dsel₁ T∈Γ D)        = 1 + D-measure D
  D-measure (dsel₂ T∈Γ D)        = 1 + D-measure D

  D-measure≥1 : ∀ {Γ S U} (D : Γ ⊢ S <: U) → D-measure D ≥ 1
  D-measure≥1 dtop           = s≤s z≤n
  D-measure≥1 dbot           = s≤s z≤n
  D-measure≥1 drefl          = s≤s z≤n
  D-measure≥1 (dtrans _ _ _) = s≤s z≤n
  D-measure≥1 (dbnd _ _)     = s≤s z≤n
  D-measure≥1 (dall _ _)     = s≤s z≤n
  D-measure≥1 (dsel₁ _ _)    = s≤s z≤n
  D-measure≥1 (dsel₂ _ _)    = s≤s z≤n

  D-deriv : Set
  D-deriv = Σ (Env × Typ × Typ) λ { (Γ , S , U) → Γ ⊢ S <: U }

  env : D-deriv → Env
  env ((Γ , _) , _) = Γ

  typ₁ : D-deriv → Typ
  typ₁ ((_ , S , U) , _) = S

  typ₂ : D-deriv → Typ
  typ₂ ((_ , S , U) , _) = U

  drefl-dec : ∀ (D : D-deriv) → Dec (D ≡ ((env D , typ₁ D , _) , drefl))
  drefl-dec (_ , dtop)         = no (λ ())
  drefl-dec (_ , dbot)         = no (λ ())
  drefl-dec (_ , drefl)        = yes refl
  drefl-dec (_ , dtrans _ _ _) = no (λ ())
  drefl-dec (_ , dbnd _ _)     = no (λ ())
  drefl-dec (_ , dall _ _)     = no (λ ())
  drefl-dec (_ , dsel₁ _ _)    = no (λ ())
  drefl-dec (_ , dsel₂ _ _)    = no (λ ())

  -- weakening
  infixl 7 _⇑
  _⇑ : Env → Env
  [] ⇑      = []
  (T ∷ Γ) ⇑ = T ↑ length Γ ∷ Γ ⇑

  ↦∈-weaken-≤ : ∀ {n T Γ} →
                  n ↦ T ∈ Γ →
                ∀ Γ₁ Γ₂ T′ →
                  Γ ≡ Γ₁ ‣ Γ₂ →
                  length Γ₂ ≤ n →
                  suc n ↦ T ↑ length Γ₂ ∈ Γ₁ ‣ T′ ! ‣ Γ₂ ⇑
  ↦∈-weaken-≤ hd .(_ ∷ _) [] T′ refl z≤n       = tl hd
  ↦∈-weaken-≤ hd Γ₁ (_ ∷ Γ₂) T′ eqΓ ()
  ↦∈-weaken-≤ (tl T∈Γ) .(_ ∷ _) [] T′ refl z≤n = tl (tl T∈Γ)
  ↦∈-weaken-≤ (tl {_} {T} T∈Γ) Γ₁ (_ ∷ Γ₂) T′ refl (s≤s l≤n)
    rewrite ↑-↑-comm T 0 (length Γ₂) z≤n       = tl (↦∈-weaken-≤ T∈Γ Γ₁ Γ₂ T′ refl l≤n)
  
  ↦∈-weaken-> : ∀ {n T Γ} →
                  n ↦ T ∈ Γ →
                ∀ Γ₁ Γ₂ T′ →
                  Γ ≡ Γ₁ ‣ Γ₂ →
                  length Γ₂ > n →
                  n ↦ T ↑ length Γ₂ ∈ Γ₁ ‣ T′ ! ‣ Γ₂ ⇑
  ↦∈-weaken-> T∈Γ Γ₁ [] T′ eqΓ ()
  ↦∈-weaken-> (hd {T}) Γ₁ (_ ∷ Γ₂) T′ refl (s≤s l>n)
    rewrite ↑-↑-comm T 0 (length Γ₂) l>n = hd
  ↦∈-weaken-> (tl {_} {T} T∈Γ) Γ₁ (_ ∷ Γ₂) T′ refl (s≤s l>n)
    rewrite ↑-↑-comm T 0 (length Γ₂) z≤n = tl (↦∈-weaken-> T∈Γ Γ₁ Γ₂ T′ refl l>n)
  
  ↦∈-weaken : ∀ {n T Γ} →
                n ↦ T ∈ Γ →
              ∀ Γ₁ Γ₂ T′ →
                Γ ≡ Γ₁ ‣ Γ₂ →
                ↑-idx n (length Γ₂) ↦ T ↑ length Γ₂ ∈ Γ₁ ‣ T′ ! ‣ Γ₂ ⇑
  ↦∈-weaken {n} T∈Γ _ Γ₂ _ eqΓ with length Γ₂ ≤? n
  ... | yes l≤n = ↦∈-weaken-≤ T∈Γ _ Γ₂ _ eqΓ l≤n
  ... | no l>n  = ↦∈-weaken-> T∈Γ _ Γ₂ _ eqΓ (≰⇒> l>n)
  
  ↦∈-weaken′ : ∀ {n T Γ} →
                 env-lookup Γ n ≡ just T →
               ∀ Γ₁ Γ₂ T′ →
                 Γ ≡ Γ₁ ‣ Γ₂ →
                 env-lookup (Γ₁ ‣ T′ ! ‣ Γ₂ ⇑) (↑-idx n (length Γ₂)) ≡ just (T ↑ length Γ₂)
  ↦∈-weaken′ T∈Γ Γ₁ Γ₂ T′ eqΓ = ↦∈⇒lookup (↦∈-weaken (lookup⇒↦∈ T∈Γ) Γ₁ Γ₂ T′ eqΓ)
  
  <:-weakening-gen : ∀ {Γ S U} →
                        Γ ⊢ S <: U →
                      ∀ Γ₁ Γ₂ T →
                        Γ ≡ Γ₁ ‣ Γ₂ →
                        Γ₁ ‣ T ! ‣ Γ₂ ⇑ ⊢ S ↑ length Γ₂ <: U ↑ length Γ₂
  <:-weakening-gen dtop Γ₁ Γ₂ T eqΓ                    = dtop
  <:-weakening-gen dbot Γ₁ Γ₂ T eqΓ                    = dbot
  <:-weakening-gen drefl Γ₁ Γ₂ T eqΓ                   = drefl
  <:-weakening-gen (dtrans T′ S<:T′ T′<:U) Γ₁ Γ₂ T eqΓ = dtrans _
                                                                (<:-weakening-gen S<:T′ Γ₁ Γ₂ T eqΓ)
                                                                (<:-weakening-gen T′<:U Γ₁ Γ₂ T eqΓ)
  <:-weakening-gen (dbnd S′<:S U<:U′) Γ₁ Γ₂ T eqΓ      = dbnd (<:-weakening-gen S′<:S Γ₁ Γ₂ T eqΓ)
                                                              (<:-weakening-gen U<:U′ Γ₁ Γ₂ T eqΓ)
  <:-weakening-gen (dall S′<:S U<:U′) Γ₁ Γ₂ T eqΓ      = dall (<:-weakening-gen S′<:S Γ₁ Γ₂ T eqΓ)
                                                              (<:-weakening-gen U<:U′ Γ₁ (_ ∷ Γ₂) T (cong (_ ∷_) eqΓ))
  <:-weakening-gen (dsel₁ {_} {n} T∈Γ T<:B) Γ₁ Γ₂ T eqΓ 
    rewrite ↑-var n (length Γ₂)                        = dsel₁ (↦∈-weaken′ T∈Γ Γ₁ Γ₂ T eqΓ)
                                                               (<:-weakening-gen T<:B Γ₁ Γ₂ T eqΓ) 
  <:-weakening-gen (dsel₂ {_} {n} T∈Γ T<:B) Γ₁ Γ₂ T eqΓ
    rewrite ↑-var n (length Γ₂)                        = dsel₂ (↦∈-weaken′ T∈Γ Γ₁ Γ₂ T eqΓ)
                                                               (<:-weakening-gen T<:B Γ₁ Γ₂ T eqΓ) 
  
  <:-weakening : ∀ {Γ₁ Γ₂ S U} T →
                    Γ₁ ‣ Γ₂ ⊢ S <: U →
                    Γ₁ ‣ T ! ‣ Γ₂ ⇑ ⊢ S ↑ length Γ₂ <: U ↑ length Γ₂
  <:-weakening T S<:U = <:-weakening-gen S<:U _ _ T refl
  
  <:-weakening-hd : ∀ {Γ S U} T →
                       Γ ⊢ S <: U →
                       Γ ‣ T ! ⊢ S ↑ 0 <: U ↑ 0
  <:-weakening-hd T = <:-weakening {Γ₂ = []} T
  
  -- narrowing
  infix 4 _≺:[_]_
  data _≺:[_]_ : Env → ℕ → Env → Set where
    ≺[_,_] : ∀ {Γ U} S → Γ ⊢ S <: U → Γ ‣ S ! ≺:[ 0 ] Γ ‣ U !
    _∷_    : ∀ {Γ₁ n Γ₂} T → Γ₁ ≺:[ n ] Γ₂ → Γ₁ ‣ T ! ≺:[ suc n ] Γ₂ ‣ T !

  <:∈-find : ∀ {x T Γ Γ′ n} →
               x ↦ T ∈ Γ →
               Γ′ ≺:[ n ] Γ →
               x ≡ n × (∃ λ T′ → n ↦ T′ ∈ Γ′ × Γ′ ⊢ T′ <: T) ⊎ x ≢ n × x ↦ T ∈ Γ′
  <:∈-find hd ≺[ T′ , T′<:T ]           = inj₁ (refl , T′ ↑ 0 , hd , <:-weakening-hd T′ T′<:T)
  <:∈-find hd (T ∷ Γ′≺:Γ)               = inj₂ ((λ ()) , hd)
  <:∈-find (tl T∈Γ) ≺[ T′ , T′<:T ]     = inj₂ ((λ ()) , tl T∈Γ)
  <:∈-find (tl T∈Γ) (S ∷ Γ′≺:Γ) with <:∈-find T∈Γ Γ′≺:Γ
  ... | inj₁ (x≡n , T′ , T′∈Γ′ , T′<:T) = inj₁ (cong suc x≡n , T′ ↑ 0 , tl T′∈Γ′ , <:-weakening-hd S T′<:T)
  ... | inj₂ (x≢n , T∈Γ′)               = inj₂ (x≢n ∘ suc-injective , tl T∈Γ′)

  <:∈-find′ : ∀ {x T Γ Γ′ n} →
                env-lookup Γ x ≡ just T →
                Γ′ ≺:[ n ] Γ →
                x ≡ n × (∃ λ T′ → env-lookup Γ′ n ≡ just T′ × Γ′ ⊢ T′ <: T) ⊎ x ≢ n × env-lookup Γ′ x ≡ just T
  <:∈-find′ T∈Γ Γ′≺Γ with <:∈-find (lookup⇒↦∈ T∈Γ) Γ′≺Γ
  ... | inj₁ (x≡n , T′ , T′∈Γ′ , T′<:T) = inj₁ (x≡n , T′ , ↦∈⇒lookup T′∈Γ′ , T′<:T)
  ... | inj₂ (x≢n , T∈Γ′)               = inj₂ (x≢n , ↦∈⇒lookup T∈Γ′)

  <:-narrow : ∀ {Γ Γ′ n S U T} →
                Γ ⊢ S <: U →
                Γ′ ≺:[ n ] Γ →
                env-lookup Γ n ≡ just T →
                Γ′ ⊢ S <: U
  <:-narrow dtop Γ′≺Γ T∈Γ                         = dtop
  <:-narrow dbot Γ′≺Γ T∈Γ                         = dbot
  <:-narrow drefl Γ′≺Γ T∈Γ                        = drefl
  <:-narrow (dtrans T S<:T T<:U) Γ′≺Γ T∈Γ         = dtrans T (<:-narrow S<:T Γ′≺Γ T∈Γ) (<:-narrow T<:U Γ′≺Γ T∈Γ)
  <:-narrow (dbnd S′<:S U<:U′) Γ′≺Γ T∈Γ           = dbnd (<:-narrow S′<:S Γ′≺Γ T∈Γ) (<:-narrow U<:U′ Γ′≺Γ T∈Γ)
  <:-narrow  {Γ} {Γ′} {n} (dall {S′ = S′} S′<:S U<:U′) Γ′≺Γ T∈Γ
    = dall (<:-narrow S′<:S Γ′≺Γ T∈Γ)
           (<:-narrow U<:U′ (_ ∷ Γ′≺Γ) (↦∈⇒lookup (tl {n} {T′ = S′} {Γ} (lookup⇒↦∈ T∈Γ))))
  <:-narrow (dsel₁ T′∈Γ T′<:B) Γ′≺Γ T∈Γ
    with <:∈-find′ T′∈Γ Γ′≺Γ
  ...  | inj₁ (refl , T″ , T″∈Γ′ , T″<:T)
    rewrite just-injective (trans (sym T′∈Γ) T∈Γ) = dsel₁ T″∈Γ′ (dtrans _ T″<:T (<:-narrow T′<:B Γ′≺Γ T∈Γ))
  ... | inj₂ (x≢n , T′∈Γ′)                        = dsel₁ T′∈Γ′ (<:-narrow T′<:B Γ′≺Γ T∈Γ)
  <:-narrow (dsel₂ T′∈Γ T′<:B) Γ′≺Γ T∈Γ
    with <:∈-find′ T′∈Γ Γ′≺Γ
  ...  | inj₁ (refl , T″ , T″∈Γ′ , T″<:T)
    rewrite just-injective (trans (sym T′∈Γ) T∈Γ) = dsel₂ T″∈Γ′ (dtrans _ T″<:T (<:-narrow T′<:B Γ′≺Γ T∈Γ))
  ... | inj₂ (x≢n , T′∈Γ′)                        = dsel₂ T′∈Γ′ (<:-narrow T′<:B Γ′≺Γ T∈Γ)

open Dsub hiding (<:-weakening-gen; <:-weakening; <:-weakening-hd
                 ; _≺:[_]_; ≺[_,_]; _∷_; <:∈-find; <:∈-find′; <:-narrow) public

-- materialization of inversion properties in invertible contexts
module DsubInvProperties {P : Env → Set}
                         (invertible : InvertibleEnv P) where

  module ContraEnvProperties = InvertibleProperties invertible _⊢_<:_
  open ContraEnvProperties public

  mutual
    <:⇒<:ᵢ : ∀ {Γ S U} → Γ ⊢ S <: U → P Γ → Γ ⊢ᵢ S <: U
    <:⇒<:ᵢ dtop pΓ                 = ditop
    <:⇒<:ᵢ dbot pΓ                 = dibot
    <:⇒<:ᵢ drefl pΓ                = direfl
    <:⇒<:ᵢ (dtrans T S<:T T<:U) pΓ = ditrans T (<:⇒<:ᵢ S<:T pΓ) (<:⇒<:ᵢ T<:U pΓ)
    <:⇒<:ᵢ (dbnd S′<:S U<:U′) pΓ   = dibnd (<:⇒<:ᵢ S′<:S pΓ) (<:⇒<:ᵢ U<:U′ pΓ)
    <:⇒<:ᵢ (dall S′<:S U<:U′) pΓ   = diall (<:⇒<:ᵢ S′<:S pΓ) U<:U′
    <:⇒<:ᵢ (dsel₁ T∈Γ T<:B) pΓ with sel-case T∈Γ T<:B pΓ
    ... | refl , _                 = dibot
    <:⇒<:ᵢ (dsel₂ T∈Γ T<:B) pΓ with sel-case T∈Γ T<:B pΓ
    ... | refl , U′ , refl
        with ⟨A:⟩<:⟨A:⟩ (<:⇒<:ᵢ T<:B pΓ) pΓ
    ...    | _ , U′<:U             = ditrans U′ (disel T∈Γ) U′<:U

    sel-case : ∀ {T Γ n S U} →
                 env-lookup Γ n ≡ just T →
                 Γ ⊢ T <: ⟨A: S ⋯ U ⟩ →
                 P Γ →
                 S ≡ ⊥ × ∃ λ U′ → T ≡ ⟨A: ⊥ ⋯ U′ ⟩
    sel-case {⊤} T∈Γ T<:B pΓ = case ⊤<: (<:⇒<:ᵢ T<:B pΓ) of λ ()
    sel-case {⊥} T∈Γ T<:B pΓ = ⊥-elim (no-⊥ pΓ T∈Γ)
    sel-case {n ∙A} T∈Γ T<:B pΓ
      with <:⟨A:⟩ (<:⇒<:ᵢ T<:B pΓ) pΓ
    ...  | inj₁ ()
    ...  | inj₂ (_ , _ , ())
    sel-case {Π S ∙ U} T∈Γ T<:B pΓ
      with <:⟨A:⟩ (<:⇒<:ᵢ T<:B pΓ) pΓ
    ...  | inj₁ ()
    ...  | inj₂ (_ , _ , ())
    sel-case {⟨A: S ⋯ U ⟩} T∈Γ T<:B pΓ
      rewrite ⊥-lb pΓ T∈Γ with ⟨A:⟩<:⟨A:⟩ (<:⇒<:ᵢ T<:B pΓ) pΓ
    ... | S<:⊥ , _ with <:⊥ S<:⊥ pΓ
    ...               | refl = refl , U , refl

  <:ᵢ⇒<: : ∀ {Γ S U} → Γ ⊢ᵢ S <: U → Γ ⊢ S <: U
  <:ᵢ⇒<: ditop                 = dtop
  <:ᵢ⇒<: dibot                 = dbot
  <:ᵢ⇒<: direfl                = drefl
  <:ᵢ⇒<: (ditrans T S<:T T<:U) = dtrans T (<:ᵢ⇒<: S<:T) (<:ᵢ⇒<: T<:U)
  <:ᵢ⇒<: (dibnd S′<:S U<:U′)   = dbnd (<:ᵢ⇒<: S′<:S) (<:ᵢ⇒<: U<:U′)
  <:ᵢ⇒<: (diall S′<:S U<:U′)   = dall (<:ᵢ⇒<: S′<:S) U<:U′
  <:ᵢ⇒<: (disel T∈Γ)           = dsel₂ T∈Γ drefl

  ⊤<:′ : ∀ {Γ T} → Γ ⊢ ⊤ <: T → P Γ → T ≡ ⊤
  ⊤<:′ ⊤<:T = ⊤<: ∘ <:⇒<:ᵢ ⊤<:T
  
  <:⊥′ : ∀ {Γ T} → Γ ⊢ T <: ⊥ → P Γ → T ≡ ⊥
  <:⊥′ T<:⊥ pΓ = <:⊥ (<:⇒<:ᵢ T<:⊥ pΓ) pΓ
  
  ⟨A:⟩<:⟨A:⟩′ : ∀ {Γ S′ U U′} → Γ ⊢ ⟨A: ⊥ ⋯ U ⟩ <: ⟨A: S′ ⋯ U′ ⟩ → P Γ →
                        S′ ≡ ⊥
  ⟨A:⟩<:⟨A:⟩′ B<:B′ pΓ with ⟨A:⟩<:⟨A:⟩ (<:⇒<:ᵢ B<:B′ pΓ) pΓ
  ... | S<:⊥ , _ = <:⊥ S<:⊥ pΓ
  
  Π<:⟨A:⟩⇒⊥ : ∀ {Γ S U S′ U′} → Γ ⊢ᵢ Π S ∙ U <: ⟨A: S′ ⋯ U′ ⟩ → P Γ → False
  Π<:⟨A:⟩⇒⊥ Π<:⟨A:⟩ eΓ with <:⟨A:⟩ Π<:⟨A:⟩ eΓ
  ... | inj₁ ()
  ... | inj₂ (_ , _ , ())
  
  ∙A<:⟨A:⟩⇒⊥ : ∀ {Γ x S U} → Γ ⊢ᵢ x ∙A <: ⟨A: S ⋯ U ⟩ → P Γ → False
  ∙A<:⟨A:⟩⇒⊥ x∙A<:⟨A:⟩ eΓ with <:⟨A:⟩ x∙A<:⟨A:⟩ eΓ
  ... | inj₁ ()
  ... | inj₂ (_ , _ , ()) 
  
  Π<:Π : ∀ {Γ S U S′ U′} →
            Γ ⊢ Π S ∙ U <: Π S′ ∙ U′ →
            P Γ →
            Γ ⊢ S′ <: S × (S′ ∷ Γ) ⊢ U <: U′
  Π<:Π <: pΓ = Σ.map₁ <:ᵢ⇒<: $ helper (<:⇒<:ᵢ <: pΓ) pΓ
    where helper : ∀ {Γ S U S′ U′} →
                     Γ ⊢ᵢ Π S ∙ U <: Π S′ ∙ U′ →
                     P Γ →
                     Γ ⊢ᵢ S′ <: S × (S′ ∷ Γ) ⊢ U <: U′
          helper direfl pΓ                           = direfl , drefl
          helper (ditrans T <: <:′) pΓ with Π<: <:
          ... | inj₁ refl                            = case ⊤<: <:′ of λ ()
          ... | inj₂ (_ , _ , refl)
              with helper <: pΓ    | helper <:′ pΓ
          ...    | S″<:S′ , U′<:U″ | S‴<:S″ , U″<:U‴ = ditrans _ S‴<:S″ S″<:S′
                                                     , dtrans _ (Dsub.<:-narrow U′<:U″ Dsub.≺[ _ , <:ᵢ⇒<: S‴<:S″ ] refl) U″<:U‴
          helper (diall <: U<:U′) pΓ                 = <: , U<:U′
