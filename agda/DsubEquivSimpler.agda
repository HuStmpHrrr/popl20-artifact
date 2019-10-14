{-# OPTIONS --without-K --safe #-}

-- This module defines D<: normal form, proves its transitivity and shows its
-- equivalence to the original D<:. It turns out that D<: normal form can be used to
-- prove undecidability.
module DsubEquivSimpler where

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
open import Dsub
open import Utils

-- D<: Normal Form
--
-- The following judgment defines D<: normal form as in Figure 4.
infix 4 _⊢″_<:_
data _⊢″_<:_ : Env → Typ → Typ → Set where
  <:⊤  : ∀ {Γ T} → Γ ⊢″ T <: ⊤
  ⊥<:  : ∀ {Γ T} → Γ ⊢″ ⊥ <: T
  refl : ∀ {Γ T} → Γ ⊢″ T <: T
  bnd  : ∀ {Γ S U S′ U′} →
           Γ ⊢″ S′ <: S →
           Γ ⊢″ U <: U′ →
           Γ ⊢″ ⟨A: S ⋯ U ⟩ <: ⟨A: S′ ⋯ U′ ⟩
  Π<:  : ∀ {Γ S U S′ U′} →
           Γ ⊢″ S′ <: S →
           Γ ‣ S′ ! ⊢″ U <: U′ →
           Γ ⊢″ Π S ∙ U <: Π S′ ∙ U′
  sel₁ : ∀ {Γ n T S} →
           env-lookup Γ n ≡ just T →
           Γ ⊢″ T <: ⟨A: S ⋯ ⊤ ⟩ →
           Γ ⊢″ S <: n ∙A
  sel₂ : ∀ {Γ n T U} →
           env-lookup Γ n ≡ just T →
           Γ ⊢″ T <: ⟨A: ⊥ ⋯ U ⟩ →
           Γ ⊢″ n ∙A <: U
  <:>  : ∀ {Γ n T S U} →
           env-lookup Γ n ≡ just T →
           Γ ⊢″ T <: ⟨A: S ⋯ ⊤ ⟩ →
           Γ ⊢″ T <: ⟨A: ⊥ ⋯ U ⟩ →
           Γ ⊢″ S <: U

-- First we show that D<: normal form admits weakening.
<:″-weakening-gen : ∀ {Γ S U} →
                      Γ ⊢″ S <: U →
                    ∀ Γ₁ Γ₂ T →
                      Γ ≡ Γ₁ ‣ Γ₂ →
                      Γ₁ ‣ T ! ‣ Γ₂ ⇑ ⊢″ S ↑ length Γ₂ <: U ↑ length Γ₂
<:″-weakening-gen <:⊤ Γ₁ Γ₂ T eqΓ               = <:⊤
<:″-weakening-gen ⊥<: Γ₁ Γ₂ T eqΓ               = ⊥<:
<:″-weakening-gen refl Γ₁ Γ₂ T eqΓ              = refl
<:″-weakening-gen (bnd S′<:S U<:U′) Γ₁ Γ₂ T eqΓ = bnd (<:″-weakening-gen S′<:S Γ₁ Γ₂ T eqΓ)
                                                      (<:″-weakening-gen U<:U′ Γ₁ Γ₂ T eqΓ)
<:″-weakening-gen (Π<: S′<:S U<:U′) Γ₁ Γ₂ T eqΓ = Π<: (<:″-weakening-gen S′<:S Γ₁ Γ₂ T eqΓ)
                                                      (<:″-weakening-gen U<:U′ Γ₁ (_ ∷ Γ₂) T (cong (_ ∷_) eqΓ))
<:″-weakening-gen (sel₁ {_} {n} T∈Γ T<:B) Γ₁ Γ₂ T eqΓ
  rewrite ↑-var n (length Γ₂)                   = sel₁ (↦∈-weaken′ T∈Γ Γ₁ Γ₂ T eqΓ)
                                                       (<:″-weakening-gen T<:B Γ₁ Γ₂ T eqΓ) 
<:″-weakening-gen (sel₂ {_} {n} T∈Γ T<:B) Γ₁ Γ₂ T eqΓ
  rewrite ↑-var n (length Γ₂)                   = sel₂ (↦∈-weaken′ T∈Γ Γ₁ Γ₂ T eqΓ)
                                                       (<:″-weakening-gen T<:B Γ₁ Γ₂ T eqΓ) 
<:″-weakening-gen (<:> {_} {n} T∈Γ T<:B T<:B′) Γ₁ Γ₂ T eqΓ
  rewrite ↑-var n (length Γ₂)                   = <:> (↦∈-weaken′ T∈Γ Γ₁ Γ₂ T eqΓ)
                                                      (<:″-weakening-gen T<:B Γ₁ Γ₂ T eqΓ)
                                                      (<:″-weakening-gen T<:B′ Γ₁ Γ₂ T eqΓ)

<:″-weakening : ∀ {Γ₁ Γ₂ S U} T →
                  Γ₁ ‣ Γ₂ ⊢″ S <: U →
                  Γ₁ ‣ T ! ‣ Γ₂ ⇑ ⊢″ S ↑ length Γ₂ <: U ↑ length Γ₂
<:″-weakening T S<:U = <:″-weakening-gen S<:U _ _ T refl

<:″-weakening-hd : ∀ {Γ S U} T →
                     Γ ⊢″ S <: U →
                     Γ ‣ T ! ⊢″ S ↑ 0 <: U ↑ 0
<:″-weakening-hd T = <:″-weakening {Γ₂ = []} T

-- Then we work on transitivity.
module SimplerTransitivity where
  -- This predicate asserts that the first context replaces _one_ type in the second
  -- context with its subtype. That is, the first context is more "precise" than the
  -- second context.
  infix 4 _≺:[_]_
  data _≺:[_]_ : Env → ℕ → Env → Set where
    ≺[_,_] : ∀ {Γ U} S → Γ ⊢″ S <: U → Γ ‣ S ! ≺:[ 0 ] Γ ‣ U !
    _∷_    : ∀ {Γ₁ n Γ₂} T → Γ₁ ≺:[ n ] Γ₂ → Γ₁ ‣ T ! ≺:[ suc n ] Γ₂ ‣ T !

  <:∈-find : ∀ {x T Γ Γ′ n} →
               x ↦ T ∈ Γ →
               Γ′ ≺:[ n ] Γ →
               x ≡ n × (∃ λ T′ → n ↦ T′ ∈ Γ′ × Γ′ ⊢″ T′ <: T) ⊎ x ≢ n × x ↦ T ∈ Γ′
  <:∈-find hd ≺[ T′ , T′<:T ]           = inj₁ (refl , T′ ↑ 0 , hd , <:″-weakening-hd T′ T′<:T)
  <:∈-find hd (T ∷ Γ′≺:Γ)               = inj₂ ((λ ()) , hd)
  <:∈-find (tl T∈Γ) ≺[ T′ , T′<:T ]     = inj₂ ((λ ()) , tl T∈Γ)
  <:∈-find (tl T∈Γ) (S ∷ Γ′≺:Γ) with <:∈-find T∈Γ Γ′≺:Γ
  ... | inj₁ (x≡n , T′ , T′∈Γ′ , T′<:T) = inj₁ (cong suc x≡n , T′ ↑ 0 , tl T′∈Γ′ , <:″-weakening-hd S T′<:T)
  ... | inj₂ (x≢n , T∈Γ′)               = inj₂ (x≢n ∘ suc-injective , tl T∈Γ′)

  <:∈-find′ : ∀ {x T Γ Γ′ n} →
                env-lookup Γ x ≡ just T →
                Γ′ ≺:[ n ] Γ →
                x ≡ n × (∃ λ T′ → env-lookup Γ′ n ≡ just T′ × Γ′ ⊢″ T′ <: T) ⊎ x ≢ n × env-lookup Γ′ x ≡ just T
  <:∈-find′ T∈Γ Γ′≺Γ with <:∈-find (lookup⇒↦∈ T∈Γ) Γ′≺Γ
  ... | inj₁ (x≡n , T′ , T′∈Γ′ , T′<:T) = inj₁ (x≡n , T′ , ↦∈⇒lookup T′∈Γ′ , T′<:T)
  ... | inj₂ (x≢n , T∈Γ′)               = inj₂ (x≢n , ↦∈⇒lookup T∈Γ′)

  private
    trans-on : Typ → Set
    trans-on T = ∀ {Γ S U} → Γ ⊢″ S <: T → Γ ⊢″ T <: U → Γ ⊢″ S <: U

    narrow-on : Typ → Set
    narrow-on T = ∀ {Γ Γ′ n S U} →
                    Γ ⊢″ S <: U →
                    Γ′ ≺:[ n ] Γ →
                    env-lookup Γ n ≡ just T →
                    Γ′ ⊢″ S <: U

  -- Per Definition 11, this defines type declaration hierarchy.
  ⟨A:⟩-layer : Typ → List Typ → Typ
  ⟨A:⟩-layer T []      = T
  ⟨A:⟩-layer T (S ∷ l) = ⟨A: S ⋯ ⟨A:⟩-layer T l ⟩

  -- Now we start proving transitivity and narrowing via a mutual induction.  This
  -- mutual induction begins exactly as presented in the paper: an induction of
  -- lexicographical order of the triple (T, 𝒟₁, 𝒟₂). Notice that this is
  -- automatically handled by Agda's termination checker, which makes the problem very
  -- nice to work with.
  --
  -- If one loads this file from Emacs, one shall see that some cases below are
  -- highlighted. The reason is that those cases are not defined
  -- _definitionally_. More details can be found in:
  -- https://agda.readthedocs.io/en/v2.5.4.2/language/function-definitions.html#case-trees.
  --
  -- In fact, those non-definitional cases hides many cases away, as they expand to
  -- numerous definitional cases, which is necessarily the case in Coq. The fact that
  -- Agda's termination checking is permissive and Agda allows non-definitional cases
  -- has significantly improved productivity of showing transitivity. In Coq, this
  -- would have required significant amount of technical setup which can easily wipe
  -- away the main idea of the proof and might not be finished within a reasonable
  -- time interval.
  mutual
    <:′-trans-rec : ∀ T → (∀ T′ → Typ-measure T′ < Typ-measure T → trans-on T′ × narrow-on T′) → trans-on T
    <:′-trans-rec (n ∙A) rec (sel₁ T∈Γ T<:B) (sel₂ T′∈Γ T<:B′)
      with ≡.trans (≡.sym T∈Γ) T′∈Γ
    ... | refl                                                           = <:> T′∈Γ T<:B T<:B′
    <:′-trans-rec ⟨A: S′ ⋯ U′ ⟩ rec (bnd S′<:S U<:U′) (bnd S″<:S U′<:U″) = bnd (<:′-trans-rec S′ (λ T′ T′<S′ → rec T′ (≤-step (≤-stepsʳ _ T′<S′))) S″<:S S′<:S)
                                                                               (<:′-trans-rec U′ (λ T′ T′<U′ → rec T′ (≤-step (≤-stepsˡ _ T′<U′))) U<:U′ U′<:U″)
    
    <:′-trans-rec (Π S′ ∙ U′) rec (Π<: S′<:S″ U″<:U′) (Π<: S‴<:S′ U′<:U‴)
      = Π<: (<:′-trans-rec S′ (λ T′ T′<S′ → rec T′ (≤-step (≤-stepsʳ _ T′<S′))) S‴<:S′ S′<:S″)
            (<:′-trans-rec U′ (λ T′ T′<U′ → rec T′ (≤-step (≤-stepsˡ _ T′<U′)))
                           (proj₂ (rec (S′ ↑ 0) (s≤s $ ≤-stepsʳ _ $ ≤-reflexive (Typ-measure-↑ S′ 0)))
                                  U″<:U′
                                  ≺[ _ , S‴<:S′ ] 
                                  refl)
                           U′<:U‴)
    
    <:′-trans-rec T rec ⊥<: T<:U                     = ⊥<:
    <:′-trans-rec T rec refl T<:U                    = T<:U
    <:′-trans-rec T rec S<:T <:⊤                     = <:⊤
    <:′-trans-rec T rec S<:T refl                    = S<:T
    <:′-trans-rec T rec (sel₂ T′∈Γ T′<:B) T<:U       = sel₂ T′∈Γ (⟨A<:⟩-traverseʳ T rec T<:U T′<:B _ refl)
    <:′-trans-rec T rec (<:> T′∈Γ T′<:B T′<:B′) T<:U = <:> T′∈Γ T′<:B (⟨A<:⟩-traverseʳ T rec T<:U T′<:B′ _ refl)
    <:′-trans-rec T rec S<:T (sel₁ T′∈Γ T′<:B)       = sel₁ T′∈Γ (⟨A<:⟩-traverseˡ T rec S<:T T′<:B [] refl)
    <:′-trans-rec T rec S<:T (<:> T′∈Γ T′<:B T′<:B′) = <:> T′∈Γ (⟨A<:⟩-traverseˡ T rec S<:T T′<:B [] refl) T′<:B′

    ⟨A<:⟩-traverseʳ : ∀ T →
                        (∀ T′ → Typ-measure T′ < Typ-measure T → trans-on T′ × narrow-on T′) →
                      ∀ {Γ U} →
                        Γ ⊢″ T <: U →
                      ∀ {S S′ T′} →
                        Γ ⊢″ S <: ⟨A: S′ ⋯ T′ ⟩ →
                      ∀ l →
                        T′ ≡ ⟨A:⟩-layer T l →
                        Γ ⊢″ S <: ⟨A: S′ ⋯ ⟨A:⟩-layer U l ⟩
    ⟨A<:⟩-traverseʳ T rec T<:U ⊥<: l eqT′                        = ⊥<:
    ⟨A<:⟩-traverseʳ T rec T<:U refl [] refl                      = bnd refl T<:U
    ⟨A<:⟩-traverseʳ T rec T<:U refl (S′ ∷ l) refl                = bnd refl (⟨A<:⟩-traverseʳ T rec T<:U refl l refl)
    ⟨A<:⟩-traverseʳ T rec T<:U (bnd S₂<:S₁ U₁<:T) [] refl        = bnd S₂<:S₁ (<:′-trans-rec T rec U₁<:T T<:U)
    ⟨A<:⟩-traverseʳ T rec T<:U (bnd S₂<:S₁ U₁<:U₂) (S′ ∷ l) refl = bnd S₂<:S₁ (⟨A<:⟩-traverseʳ T rec T<:U U₁<:U₂ l refl)
    ⟨A<:⟩-traverseʳ T rec T<:U (sel₂ T′∈Γ T′<:B) l refl          = sel₂ T′∈Γ (⟨A<:⟩-traverseʳ T rec T<:U T′<:B (_ ∷ l) refl)
    ⟨A<:⟩-traverseʳ T rec T<:U (<:> T′∈Γ T′<:B T′<:B′) l refl    = <:> T′∈Γ T′<:B (⟨A<:⟩-traverseʳ T rec T<:U T′<:B′ (_ ∷ l) refl)

    ⟨A<:⟩-traverseˡ : ∀ T →
                        (∀ T′ → Typ-measure T′ < Typ-measure T → trans-on T′ × narrow-on T′) →
                      ∀ {Γ S} →
                        Γ ⊢″ S <: T →
                      ∀ {S′ T′} →
                        Γ ⊢″ S′ <: T′ →
                      ∀ {U} l →
                        T′ ≡ ⟨A:⟩-layer ⟨A: T ⋯ U ⟩ l →
                        Γ ⊢″ S′ <: ⟨A:⟩-layer ⟨A: S ⋯ U ⟩ l
    ⟨A<:⟩-traverseˡ T rec S<:T <:⊤ [] ()
    ⟨A<:⟩-traverseˡ T rec S<:T <:⊤ (_ ∷ l) ()
    ⟨A<:⟩-traverseˡ T rec S<:T ⊥<: l eqT′                        = ⊥<:
    ⟨A<:⟩-traverseˡ T rec S<:T refl [] refl                      = bnd S<:T refl
    ⟨A<:⟩-traverseˡ T rec S<:T refl (S′ ∷ l) refl                = bnd refl (⟨A<:⟩-traverseˡ T rec S<:T refl l refl)
    ⟨A<:⟩-traverseˡ T rec S<:T (bnd T<:S₁ U₁<:U₂) [] refl        = bnd (<:′-trans-rec T rec S<:T T<:S₁) U₁<:U₂
    ⟨A<:⟩-traverseˡ T rec S<:T (bnd S₂<:S₁ U₁<:U₂) (S′ ∷ l) refl = bnd S₂<:S₁ (⟨A<:⟩-traverseˡ T rec S<:T U₁<:U₂ l refl)
    ⟨A<:⟩-traverseˡ T rec S<:T (Π<: S₂<:S₁ U₁<:U₂) [] ()
    ⟨A<:⟩-traverseˡ T rec S<:T (Π<: S₂<:S₁ U₁<:U₂) (_ ∷ l) ()
    ⟨A<:⟩-traverseˡ T rec S<:T (sel₁ T′∈Γ T′<:B) [] ()
    ⟨A<:⟩-traverseˡ T rec S<:T (sel₁ T′∈Γ T′<:B) (_ ∷ l) ()
    ⟨A<:⟩-traverseˡ T rec S<:T (sel₂ T′∈Γ T′<:B) {U} l refl      = sel₂ T′∈Γ (⟨A<:⟩-traverseˡ T rec S<:T T′<:B {U} (_ ∷ l) refl)
    ⟨A<:⟩-traverseˡ T rec S<:T (<:> T′∈Γ T′<:B T′<:B′) l refl    = <:> T′∈Γ T′<:B (⟨A<:⟩-traverseˡ T rec S<:T T′<:B′ (_ ∷ l) refl)

  <:″-narrow-on : ∀ T → (∀ T′ → Typ-measure T′ ≡ Typ-measure T → trans-on T′) → narrow-on T
  <:″-narrow-on T trans <:⊤ Γ′≺Γ T∈Γ               = <:⊤
  <:″-narrow-on T trans ⊥<: Γ′≺Γ T∈Γ               = ⊥<:
  <:″-narrow-on T trans refl Γ′≺Γ T∈Γ              = refl
  <:″-narrow-on T trans (bnd S′<:S U<:U′) Γ′≺Γ T∈Γ = bnd (<:″-narrow-on T trans S′<:S Γ′≺Γ T∈Γ)
                                                         (<:″-narrow-on T trans U<:U′ Γ′≺Γ T∈Γ)
  <:″-narrow-on T trans {Γ} {Γ′} {n} (Π<: {S′ = S′} S′<:S U<:U′) Γ′≺Γ T∈Γ
    = Π<: (<:″-narrow-on T trans S′<:S Γ′≺Γ T∈Γ)
          (<:″-narrow-on (T ↑ 0)
                         (λ T′ eq → trans T′ (≡.trans eq (Typ-measure-↑ T 0)))
                         U<:U′ (_ ∷ Γ′≺Γ)
                         (↦∈⇒lookup (tl {n} {T′ = S′} {Γ} (lookup⇒↦∈ T∈Γ))))
  
  <:″-narrow-on T trans (sel₁ T′∈Γ T′<:B) Γ′≺Γ T∈Γ
    with <:∈-find′ T′∈Γ Γ′≺Γ
  ...  | inj₁ (refl , T″ , T″∈Γ′ , T″<:T)
    rewrite just-injective (≡.trans (≡.sym T′∈Γ) T∈Γ) = sel₁ T″∈Γ′ (trans T refl T″<:T (<:″-narrow-on T trans T′<:B Γ′≺Γ T∈Γ))
  ... | inj₂ (x≢n , T′∈Γ′)                            = sel₁ T′∈Γ′ (<:″-narrow-on T trans T′<:B Γ′≺Γ T∈Γ)
  <:″-narrow-on T trans (sel₂ T′∈Γ T′<:B) Γ′≺Γ T∈Γ
    with <:∈-find′ T′∈Γ Γ′≺Γ
  ...  | inj₁ (refl , T″ , T″∈Γ′ , T″<:T)
    rewrite just-injective (≡.trans (≡.sym T′∈Γ) T∈Γ) = sel₂ T″∈Γ′ (trans T refl T″<:T (<:″-narrow-on T trans T′<:B Γ′≺Γ T∈Γ))
  ... | inj₂ (x≢n , T′∈Γ′)                            = sel₂ T′∈Γ′ (<:″-narrow-on T trans T′<:B Γ′≺Γ T∈Γ)
  <:″-narrow-on T trans (<:> T′∈Γ T′<:B T′<:B′) Γ′≺Γ T∈Γ
    with <:∈-find′ T′∈Γ Γ′≺Γ
  ...  | inj₁ (refl , T″ , T″∈Γ′ , T″<:T)
    rewrite just-injective (≡.trans (≡.sym T′∈Γ) T∈Γ) = <:> T″∈Γ′
                                                            (trans T refl T″<:T (<:″-narrow-on T trans T′<:B Γ′≺Γ T∈Γ))
                                                            (trans T refl T″<:T (<:″-narrow-on T trans T′<:B′ Γ′≺Γ T∈Γ))
  ... | inj₂ (x≢n , T′∈Γ′)                            = <:> T′∈Γ′
                                                            (<:″-narrow-on T trans T′<:B Γ′≺Γ T∈Γ)
                                                            (<:″-narrow-on T trans T′<:B′ Γ′≺Γ T∈Γ)

  -- The previous functions achieve the inductive hypotheses of the well-founded
  -- induction on the size of the type T, and the following function combines those
  -- inductive hypotheses and conclude transitivity and narrowing.
  <:″-trans-narrow : ∀ T → trans-on T × narrow-on T
  <:″-trans-narrow = wfRec _ aux
    where open Measure <-wellFounded Typ-measure
          aux : ∀ T → (∀ T′ → Typ-measure T′ < Typ-measure T → trans-on T′ × narrow-on T′) → trans-on T × narrow-on T
          aux T rec = <:′-trans-rec T rec
                    , <:″-narrow-on T (λ T′ T′≡T →
                                         <:′-trans-rec T′ λ T″ T″<T′ → rec T″ (≤-trans T″<T′ (≤-reflexive T′≡T)))

  <:″-trans : ∀ {T} → trans-on T
  <:″-trans {T} = proj₁ (<:″-trans-narrow T)

  <:″-narrow : ∀ {T} → narrow-on T
  <:″-narrow {T} = proj₂ (<:″-trans-narrow T)

open SimplerTransitivity using (<:″-trans ; <:″-narrow) public

-- the following two functions show that the original D<: and D<: normal form are
-- equivalent.
<:⇒<:″ : ∀ {Γ S U} → Γ ⊢ S <: U → Γ ⊢″ S <: U
<:⇒<:″ dtop                 = <:⊤
<:⇒<:″ dbot                 = ⊥<:
<:⇒<:″ drefl                = refl
<:⇒<:″ (dtrans T S<:T T<:U) = <:″-trans (<:⇒<:″ S<:T) (<:⇒<:″ T<:U)
<:⇒<:″ (dbnd S′<:S U<:U′)   = bnd (<:⇒<:″ S′<:S) (<:⇒<:″ U<:U′)
<:⇒<:″ (dall S′<:S U<:U′)   = Π<: (<:⇒<:″ S′<:S) (<:⇒<:″ U<:U′)
<:⇒<:″ (dsel₁ T∈Γ T<:B)     = sel₁ T∈Γ (<:⇒<:″ T<:B)
<:⇒<:″ (dsel₂ T∈Γ T<:B)     = sel₂ T∈Γ (<:⇒<:″ T<:B)

<:″⇒<: : ∀ {Γ S U} → Γ ⊢″ S <: U → Γ ⊢ S <: U
<:″⇒<: <:⊤                  = dtop
<:″⇒<: ⊥<:                  = dbot
<:″⇒<: refl                 = drefl
<:″⇒<: (bnd S′<:S U<:U′)    = dbnd (<:″⇒<: S′<:S) (<:″⇒<: U<:U′)
<:″⇒<: (Π<: S′<:S U<:U′)    = dall (<:″⇒<: S′<:S) (<:″⇒<: U<:U′)
<:″⇒<: (sel₁ T∈Γ T<:B)      = dsel₁ T∈Γ (<:″⇒<: T<:B)
<:″⇒<: (sel₂ T∈Γ T<:B)      = dsel₂ T∈Γ (<:″⇒<: T<:B)
<:″⇒<: (<:> T∈Γ T<:B S<:B′) = dtrans _ (dsel₁ T∈Γ (dtrans _ (<:″⇒<: T<:B) (dbnd drefl dtop)))
                                       (dsel₂ T∈Γ (dtrans _ (<:″⇒<: S<:B′) (dbnd dbot drefl)))
-- D<: subtyping is undecidable.
module Undecidability′ where
  open import DsubReduced
  open FsubMinusToDsubR using (⟦_⟧ ; ⟪_⟫ ; D<:ᵣ⇒F<: ; F<:⇒D<:ᵣ ; ⟪⟫-contraEnv ; ⟦⟧-covar)
  open DsubInvProperties contraInvertible
  open import FsubMinus

  <:″⇒<:ᵣ : ∀ {Γ S U} →
              Γ ⊢″ S <: U →
              ContraEnv Γ → Covar S → Covar U →
              Γ ⊢ᵣ S <: U
  <:″⇒<:ᵣ <:⊤ cΓ cS cU                                           = drtop cS
  <:″⇒<:ᵣ ⊥<: cΓ () cU
  <:″⇒<:ᵣ refl cΓ cS cU                                          = drrefl cU
  <:″⇒<:ᵣ (bnd S′<:S U<:U′) cΓ cS ()
  <:″⇒<:ᵣ (Π<: <:⊤ U<:U′) cΓ () cU
  <:″⇒<:ᵣ (Π<: ⊥<: U<:U′) cΓ cS ()
  <:″⇒<:ᵣ (Π<: refl U<:U′) cΓ (cvΠ cS cU) (cvΠ cS′ cU′)          = drall cS′ cU cS′ cU′
                                                                         (drrefl cS′)
                                                                         (<:″⇒<:ᵣ U<:U′ (ctt cS′ ∷ cΓ) cU cU′)
  <:″⇒<:ᵣ (Π<: (bnd _ S′<:S) U<:U′) cΓ (cvΠ cS cU) (cvΠ cS′ cU′) = drall cS cU cS′ cU′
                                                                         (<:″⇒<:ᵣ S′<:S cΓ cS′ cS)
                                                                         (<:″⇒<:ᵣ U<:U′ (ctt cS′ ∷ cΓ) cU cU′)
  <:″⇒<:ᵣ (Π<: (Π<: S′<:S S′<:S₁) U<:U′) cΓ () cU
  <:″⇒<:ᵣ (Π<: (sel₁ x S′<:S) U<:U′) cΓ () cU
  <:″⇒<:ᵣ (Π<: (sel₂ x S′<:S) U<:U′) cΓ cS ()
  <:″⇒<:ᵣ (Π<: (<:> T∈Γ T<:B T<:B′) U<:U′) cΓ (cvΠ _ _) (cvΠ _ _)
    with lookupContraEnv T∈Γ cΓ
  ... | ctt _                                                    = case ⟨A:⟩<:⟨A:⟩′ (<:″⇒<: T<:B) cΓ of λ ()
  <:″⇒<:ᵣ (sel₁ T∈Γ T<:B) cΓ cS cU
    with lookupContraEnv T∈Γ cΓ
  ... | ctt _  rewrite ⟨A:⟩<:⟨A:⟩′ (<:″⇒<: T<:B) cΓ              = case cS of λ ()
  <:″⇒<:ᵣ (sel₂ T∈Γ T<:B) cΓ cS cU
    with lookupContraEnv T∈Γ cΓ
  ... | ctt cT                                                   = drsel T∈Γ cT (aux T<:B cΓ cT cU)
    where aux : ∀ {Γ T S U} → Γ ⊢″ ⟨A: ⊥ ⋯ T ⟩ <: ⟨A: S ⋯ U ⟩ → ContraEnv Γ → Covar T → Covar U → Γ ⊢ᵣ T <: U
          aux refl cΓ cT cU                                      = drrefl cU
          aux (bnd _ T<:U) cΓ cT cU                              = <:″⇒<:ᵣ T<:U cΓ cT cU
          aux (<:> T′∈Γ T′<:B _) cΓ cT cU
            with lookupContraEnv T′∈Γ cΓ
          ... | ctt _                                            = case ⟨A:⟩<:⟨A:⟩′ (<:″⇒<: T′<:B) cΓ of λ ()
  <:″⇒<:ᵣ (<:> T∈Γ T<:B T<:B′) cΓ cS cU
    with lookupContraEnv T∈Γ cΓ
  ... | ctt _  rewrite ⟨A:⟩<:⟨A:⟩′ (<:″⇒<: T<:B) cΓ              = case cS of λ ()

  <:ᵣ⇒<: : ∀ {Γ S U} → Γ ⊢ᵣ S <: U → Γ ⊢ S <: U
  <:ᵣ⇒<: (drtop _)                   = dtop
  <:ᵣ⇒<: (drrefl _)                  = drefl
  <:ᵣ⇒<: (drall _ _ _ _ S′<:S U<:U′) = dall (dbnd dbot (<:ᵣ⇒<: S′<:S)) (<:ᵣ⇒<: U<:U′)
  <:ᵣ⇒<: (drsel T∈Γ _ T<:B)          = dtrans _ (dsel₂ T∈Γ drefl) (<:ᵣ⇒<: T<:B)

  open FsubMinus.FsubMinus

  F<:⇒D<: : ∀ {Γ S U} → Γ ⊢F S <: U → ⟪ Γ ⟫ ⊢ ⟦ S ⟧ <: ⟦ U ⟧
  F<:⇒D<: = <:ᵣ⇒<: ∘ F<:⇒D<:ᵣ

  D<:⇒F<: : ∀ {Γ S U} → ⟪ Γ ⟫ ⊢ ⟦ S ⟧ <: ⟦ U ⟧ → Γ ⊢F S <: U
  D<:⇒F<: S<:U = D<:ᵣ⇒F<: (<:″⇒<:ᵣ (<:⇒<:″ S<:U) (⟪⟫-contraEnv _) (⟦⟧-covar _) (⟦⟧-covar _))
                          refl refl refl
