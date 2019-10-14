{-# OPTIONS --without-K --safe #-}

-- Properties of F<:⁻
--
-- This file shows several structural properties of F<:⁻, including weakening,
-- narrowing and transitivity. They are not used anywhere, but just serve as a
-- reference to compare the complexity with the corresponding proofs of D<:.
module FsubMinus2 where

open import Data.List as List
open import Data.Nat
open import Data.Maybe as Maybe
open import Data.Product
open import Data.Sum
open import Function
open import Data.Empty renaming (⊥ to False)

open import Relation.Nullary
open import Relation.Binary.PropositionalEquality as ≡

open import Data.Nat.Properties as ℕₚ
open import Data.Maybe.Properties as Maybeₚ
open import Utils
open import FsubMinus
open import Data.List.Properties as Listₚ

open import Induction.Nat

open FsubMinus.FsubMinus

infixl 7 _⇑

Γ-⇑ : Env → Ftyp → Ftyp
Γ-⇑ Γ = _↑ length Γ

_⇑ : Env → Env
[] ⇑      = []
(T ∷ Γ) ⇑ = Γ-⇑ Γ T ∷ Γ ⇑

↑-↑-comm : ∀ T m n → m ≤ n → T ↑ m ↑ suc n ≡ T ↑ n ↑ m
↑-↑-comm ⊤ m n m≤n                                  = refl
↑-↑-comm (var x) m n m≤n with n ≤? x
... | yes n≤x
  rewrite ≤?-yes $ ≤-step $ ≤-trans m≤n n≤x
        | ≤?-yes $ ≤-trans m≤n n≤x
        | ≤?-yes n≤x                                = refl
... | no x<n with m ≤? x
...             | yes m≤x rewrite proj₂ $ ≤?-no x<n = refl
...             | no x<m with suc n ≤? x
...                         | yes 1+n≤x             = ⊥-elim $ x<m (≤-trans (≤-step m≤n) 1+n≤x)
...                         | no x<1+n              = refl
↑-↑-comm (Π<: S ∙ U) m n m≤n
  rewrite ↑-↑-comm S m n m≤n
        | ↑-↑-comm U (suc m) (suc n) (s≤s m≤n)      = refl

<:∈-weakening-≤ : ∀ {x T Γ} →
                  x <: T ∈ Γ →
                  ∀ Γ₁ Γ₂ T′ →
                  Γ ≡ Γ₁ ‣ Γ₂ →
                  length Γ₂ ≤ x →
                  suc x <: Γ-⇑ Γ₂ T ∈ Γ₁ ‣ T′ ! ‣ Γ₂ ⇑
<:∈-weakening-≤ hd Γ₁ [] T′ refl l≤x       = tl hd
<:∈-weakening-≤ hd Γ₁ (_ ∷ Γ₂) T′ eq ()
<:∈-weakening-≤ (tl <:∈) Γ₁ [] T′ refl l≤x = tl (tl <:∈)
<:∈-weakening-≤ (tl {T = T} <:∈) Γ₁ (_ ∷ Γ₂) T′ refl (s≤s l≤x)
  rewrite ↑-↑-comm T 0 (length Γ₂) z≤n     = tl $ <:∈-weakening-≤ <:∈ Γ₁ Γ₂ T′ refl l≤x

<:∈-weakening-> : ∀ {x T Γ} →
                  x <: T ∈ Γ →
                  ∀ Γ₁ Γ₂ T′ →
                  Γ ≡ Γ₁ ‣ Γ₂ →
                  length Γ₂ > x →
                  x <: Γ-⇑ Γ₂ T ∈ Γ₁ ‣ T′ ! ‣ Γ₂ ⇑
<:∈-weakening-> hd Γ₁ [] T′ eq ()
<:∈-weakening-> hd Γ₁ (T ∷ Γ₂) T′ refl l>x
  rewrite ↑-↑-comm T 0 (length Γ₂) z≤n = hd
<:∈-weakening-> (tl <:∈) Γ₁ [] T′ eq ()
<:∈-weakening-> (tl {T = T} <:∈) Γ₁ (_ ∷ Γ₂) T′ refl (s≤s l>x)
  rewrite ↑-↑-comm T 0 (length Γ₂) z≤n = tl $ <:∈-weakening-> <:∈ Γ₁ Γ₂ T′ refl l>x

<:∈-weakening : ∀ {x T Γ} →
                  x <: T ∈ Γ →
                  ∀ Γ₁ Γ₂ T′ →
                  Γ ≡ Γ₁ ‣ Γ₂ →
                  ↑-idx x (length Γ₂) <: Γ-⇑ Γ₂ T ∈ Γ₁ ‣ T′ ! ‣ Γ₂ ⇑
<:∈-weakening {x} <:∈ Γ₁ Γ₂ T′ eq with length Γ₂ ≤? x
... | yes p = <:∈-weakening-≤ <:∈ Γ₁ Γ₂ T′ eq p
... | no ¬p = <:∈-weakening-> <:∈ Γ₁ Γ₂ T′ eq (≰⇒> ¬p)

<:-weakening-gen : ∀ {Γ S U} →
              Γ ⊢F S <: U →
              ∀ Γ₁ Γ₂ T →
                Γ ≡ Γ₁ ‣ Γ₂ →
                Γ₁ ‣ T ! ‣ Γ₂ ⇑ ⊢F Γ-⇑ Γ₂ S <: Γ-⇑ Γ₂ U
<:-weakening-gen ftop Γ₁ Γ₂ T eq = ftop
<:-weakening-gen (fvrefl {_} {x}) Γ₁ Γ₂ T eq
  rewrite ↑-var x (length Γ₂)    = fvrefl
<:-weakening-gen (fbinds {_} {x} T∈Γ D) Γ₁ Γ₂ T eq
  rewrite ↑-var x (length Γ₂)    = fbinds (<:∈-weakening T∈Γ Γ₁ Γ₂ T eq)
                                          (<:-weakening-gen D Γ₁ Γ₂ T eq)
<:-weakening-gen (fall {S₂ = S₂} Dp Db) Γ₁ Γ₂ T eq
  = fall (<:-weakening-gen Dp Γ₁ Γ₂ T eq)
         (<:-weakening-gen Db Γ₁ (Γ₂ ‣ S₂ !) T (cong (S₂ ∷_) eq))

<:-weakening : ∀ {S U} Γ₁ Γ₂ T →
              Γ₁ ‣ Γ₂ ⊢F S <: U →
              Γ₁ ‣ T ! ‣ Γ₂ ⇑ ⊢F Γ-⇑ Γ₂ S <: Γ-⇑ Γ₂ U
<:-weakening _ _ T D = <:-weakening-gen D _ _ T refl

<:-weakening-hd : ∀ {Γ S U} T →
                 Γ ⊢F S <: U →
                 Γ ‣ T ! ⊢F S ↑ 0 <: U ↑ 0
<:-weakening-hd T D = <:-weakening _ [] T D

<:-weakening′ : ∀ {Γ S U} Γ′ →
               Γ ⊢F S <: U →
               Γ ‣ Γ′ ⊢F repeat (length Γ′) (_↑ 0) S <: repeat (length Γ′) (_↑ 0) U
<:-weakening′ [] D       = D
<:-weakening′ (T ∷ Γ′) D = <:-weakening-hd T $ <:-weakening′ Γ′ D

<:-refl : ∀ Γ T → Γ ⊢F T <: T
<:-refl Γ ⊤           = ftop
<:-refl Γ (var x)     = fvrefl
<:-refl Γ (Π<: S ∙ U) = fall (<:-refl Γ S) (<:-refl (S ∷ Γ) U)

module TransProof where
  open ≤-Reasoning

  <:∈-find : ∀ {x T Γ} →
               x <: T ∈ Γ →
               ∀ T₁ T₂ Γ₁ Γ₂ →
                 Γ ≡ Γ₁ ‣ T₁ ! ‣ Γ₂ →
                 x ≢ length Γ₂ × x <: T ∈ Γ₁ ‣ T₂ ! ‣ Γ₂ ⊎
                 x ≡ length Γ₂ × T ≡ repeat (suc (length Γ₂)) (_↑ 0) T₁ ×
                 x <: repeat (suc (length Γ₂)) (_↑ 0) T₂ ∈ Γ₁ ‣ T₂ ! ‣ Γ₂
  <:∈-find hd T₁ T₂ Γ₁ [] refl       = inj₂ (refl , refl , hd)
  <:∈-find hd T₁ T₂ Γ₁ (_ ∷ Γ₂) refl = inj₁ ((λ ()) , hd)
  <:∈-find (tl <:∈) T₁ T₂ Γ₁ [] refl = inj₁ ((λ ()) , tl <:∈)
  <:∈-find (tl <:∈) T₁ T₂ Γ₁ (_ ∷ Γ₂) refl with <:∈-find <:∈ T₁ T₂ Γ₁ Γ₂ refl
  ... | inj₁ (n≢l , r)               = inj₁ ((λ n≡l → n≢l (suc-injective n≡l)) , tl r)
  ... | inj₂ (n≡l , e , r)           = inj₂ (cong suc n≡l , cong (_↑ 0) e , tl r)

  infix 4 _≺:[_]_
  data _≺:[_]_ : Env → ℕ → Env → Set where
    ≺[_,_] : ∀ {Γ U} S → Γ ⊢F S <: U → Γ ‣ S ! ≺:[ 0 ] Γ ‣ U !
    _∷_    : ∀ {Γ₁ n Γ₂} T → Γ₁ ≺:[ n ] Γ₂ → Γ₁ ‣ T ! ≺:[ suc n ] Γ₂ ‣ T !

  <:∈-find′ : ∀ {x T Γ Γ′ n} →
               x <: T ∈ Γ →
               Γ′ ≺:[ n ] Γ →
               x ≡ n × (∃ λ T′ → n <: T′ ∈ Γ′ × Γ′ ⊢F T′ <: T) ⊎ x ≢ n × x <: T ∈ Γ′
  <:∈-find′ hd ≺[ T′ , T′<:T ]          = inj₁ (refl , T′ ↑ 0 , hd , <:-weakening-hd T′ T′<:T)
  <:∈-find′ hd (T ∷ Γ′≺:Γ)              = inj₂ ((λ ()) , hd)
  <:∈-find′ (tl T∈Γ) ≺[ T′ , T′<:T ]    = inj₂ ((λ ()) , tl T∈Γ)
  <:∈-find′ (tl T∈Γ) (S ∷ Γ′≺:Γ) with <:∈-find′ T∈Γ Γ′≺:Γ
  ... | inj₁ (x≡n , T′ , T′∈Γ′ , T′<:T) = inj₁ (cong suc x≡n , T′ ↑ 0 , tl T′∈Γ′ , <:-weakening-hd S T′<:T)
  ... | inj₂ (x≢n , T∈Γ′)               = inj₂ (x≢n ∘ suc-injective , tl T∈Γ′)

  trans-on : Ftyp → Set
  trans-on T = ∀ {Γ S U} → Γ ⊢F S <: T → Γ ⊢F T <: U → Γ ⊢F S <: U

  narrow-on : Ftyp → Set
  narrow-on T = ∀ {Γ Γ′ n S U} →
                  Γ ⊢F S <: U →
                  Γ′ ≺:[ n ] Γ →
                  n <: T ∈ Γ →
                  Γ′ ⊢F S <: U

  <:-trans-rec : ∀ T → (∀ T′ → Ftyp-measure T′ < Ftyp-measure T → trans-on T′ × narrow-on T′) → trans-on T
  <:-trans-rec ⊤ rec S<:T ftop                                 = S<:T
  <:-trans-rec (var x) rec S<:T ftop                           = ftop
  <:-trans-rec (var x) rec S<:T fvrefl                         = S<:T
  <:-trans-rec (var x) rec fvrefl (fbinds T∈Γ T<:U)            = fbinds T∈Γ T<:U
  <:-trans-rec (var x) rec (fbinds S∈Γ S<:T) (fbinds T∈Γ T<:U) = fbinds S∈Γ (<:-trans-rec (var x) rec S<:T (fbinds T∈Γ T<:U))
  <:-trans-rec (Π<: S ∙ U) rec S<:T ftop                       = ftop
  <:-trans-rec (Π<: S ∙ U) rec (fbinds S∈Γ S<:T) (fall Db Dp)  = fbinds S∈Γ (<:-trans-rec (Π<: S ∙ U) rec S<:T (fall Db Dp))
  <:-trans-rec (Π<: S ∙ U) rec (fall Dp₁ Db₁) (fall Dp₂ Db₂)   = fall (<:-trans-rec S (λ T′ T′<:S → rec T′ (≤-stepsʳ _ T′<:S)) Dp₂ Dp₁)
                                                                      (<:-trans-rec U
                                                                                    (λ T′ T′<U → rec T′ (≤-trans T′<U (≤-stepsˡ _ ≤-refl)))
                                                                                    (proj₂ (rec (S ↑ 0) S↑0<SU) Db₁ ≺[ _ , Dp₂ ] hd)
                                                                                    Db₂)
    where S↑0<SU : Ftyp-measure (S ↑ 0) < Ftyp-measure S + Ftyp-measure U
          S↑0<SU = begin-strict
            Ftyp-measure (S ↑ 0)            ≡⟨ Ftyp-measure-↑ S 0 ⟩
            Ftyp-measure S                  <⟨ ≤-refl ⟩
            1 + Ftyp-measure S              ≡⟨ sym (+-comm _ 1) ⟩
            Ftyp-measure S + 1              ≤⟨ +-monoʳ-≤ _ (Ftyp-measure≥1 U) ⟩
            Ftyp-measure S + Ftyp-measure U ∎

  <:-narrowing-rec : ∀ T → (∀ T′ → Ftyp-measure T′ ≤ Ftyp-measure T → trans-on T′) → narrow-on T
  <:-narrowing-rec T trans ftop Γ′≺:Γ T∈Γ         = ftop
  <:-narrowing-rec T trans fvrefl Γ′≺:Γ T∈Γ       = fvrefl
  <:-narrowing-rec T trans (fbinds S∈Γ S<:U) Γ′≺:Γ T∈Γ with <:∈-find′ S∈Γ Γ′≺:Γ
  ... | inj₁ (refl , T′ , T′∈Γ′ , T′<:T)
    rewrite <:∈-func S∈Γ T∈Γ                      = fbinds T′∈Γ′ (trans T ≤-refl
                                                                          T′<:T
                                                                          (<:-narrowing-rec T trans S<:U Γ′≺:Γ T∈Γ))
  ... | inj₂ (x≢n , T′∈Γ′)                        = fbinds T′∈Γ′ (<:-narrowing-rec T trans S<:U Γ′≺:Γ T∈Γ)
  <:-narrowing-rec T trans (fall Dp Db) Γ′≺:Γ T∈Γ = fall (<:-narrowing-rec T trans Dp Γ′≺:Γ T∈Γ)
                                                         (<:-narrowing-rec (T ↑ 0)
                                                                           (λ T′ → trans T′ ∘ T′≤T T′)
                                                                           Db (_ ∷ Γ′≺:Γ) (tl T∈Γ))
    where T′≤T : ∀ T′ → Ftyp-measure T′ ≤ Ftyp-measure (T ↑ 0) → Ftyp-measure T′ ≤ Ftyp-measure T
          T′≤T T′ T′≤T↑0 = begin
            Ftyp-measure T′      ≤⟨ T′≤T↑0 ⟩
            Ftyp-measure (T ↑ 0) ≡⟨ Ftyp-measure-↑ T 0 ⟩
            Ftyp-measure T       ∎

  <:-trans-narrow : ∀ T → trans-on T × narrow-on T
  <:-trans-narrow = wfRec (λ T → trans-on T × narrow-on T)
                          λ T rec →
                            <:-trans-rec T rec ,
                            <:-narrowing-rec T λ T′ T′≤T →
                                                 <:-trans-rec T′ λ T″ T″<T′ →
                                                                   rec T″ (≤-trans T″<T′ T′≤T)
    where open Measure <-wellFounded Ftyp-measure

  <:-trans : ∀ {T} → trans-on T
  <:-trans {T} = proj₁ $ <:-trans-narrow T

  <:-narrow : ∀ {T} → narrow-on T
  <:-narrow {T} = proj₂ $ <:-trans-narrow T

<:-weakening-size-gen : ∀ {Γ S U} →
                          (S<:U : Γ ⊢F S <: U) →
                          ∀ Γ₁ Γ₂ T →
                            (eq : Γ ≡ Γ₁ ‣ Γ₂) →
                            F-measure S<:U ≡ F-measure (<:-weakening-gen S<:U Γ₁ Γ₂ T eq)
<:-weakening-size-gen ftop Γ₁ Γ₂ T eq = refl
<:-weakening-size-gen (fvrefl {_} {x}) Γ₁ Γ₂ T eq
  rewrite ↑-var x (length Γ₂)         = refl
<:-weakening-size-gen (fbinds {_} {x} S∈Γ D) Γ₁ Γ₂ T eq
  rewrite ↑-var x (length Γ₂)         = cong suc (<:-weakening-size-gen D Γ₁ Γ₂ T eq)
<:-weakening-size-gen (fall {S₂ = S} Dp Db) Γ₁ Γ₂ T eq
  = cong suc (cong₂ _+_ (<:-weakening-size-gen Dp Γ₁ Γ₂ T eq)
                        (<:-weakening-size-gen Db Γ₁ (S ∷ Γ₂) T (cong (S ∷_) eq)))

open TransProof using (<:-trans ; <:-narrow) public
