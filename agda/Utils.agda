{-# OPTIONS --without-K --safe #-}

-- This is a utility module.
module Utils where

open import Induction.WellFounded as Wf
open import Data.List as List
open import Data.List.All
open import Data.Nat
open import Data.Maybe
open import Data.Product as ,
open import Data.Empty
open import Function

open import Relation.Nullary
open import Relation.Binary
open import Relation.Binary.PropositionalEquality

infix 6 _!
_! : ∀ {a} {A : Set a} → A → List A
a ! = a ∷ []

infixl 5 _‣_
_‣_ : ∀ {a} {A : Set a} → List A → List A → List A
l₁ ‣ l₂ = l₂ ++ l₁

lookupOpt : ∀ {a} {A : Set a} → List A → ℕ → Maybe A
lookupOpt [] n            = nothing
lookupOpt (x ∷ l) zero    = just x
lookupOpt (x ∷ l) (suc n) = lookupOpt l n

module _ {a} {A : Set a} where
  lookupOpt-map-inv : ∀ {b} {B : Set b} {f : A → B} l {n e} →
                        lookupOpt (List.map f l) n ≡ just e →
                        ∃[ e' ] (e ≡ f e' × lookupOpt l n ≡ just e')
  lookupOpt-map-inv [] {n} ()
  lookupOpt-map-inv (x ∷ l) {zero} refl = x , refl , refl
  lookupOpt-map-inv (x ∷ l) {suc n} eq  = lookupOpt-map-inv l eq
  
  lookupOpt-map : ∀ {b} {B : Set b} l (f : A → B) {n e} →
                    lookupOpt l n ≡ just e → 
                    lookupOpt (List.map f l) n ≡ just (f e)
  lookupOpt-map [] f ()
  lookupOpt-map (x ∷ l) f {zero} refl = refl
  lookupOpt-map (x ∷ l) f {suc n} eq  = lookupOpt-map l f eq
  
  lookupOpt-All : ∀ {b} {P : A → Set b} {l n e} →
                    lookupOpt l n ≡ just e →
                    All P l →
                    P e
  lookupOpt-All {n = n} () []
  lookupOpt-All {n = zero} refl (px ∷ all) = px
  lookupOpt-All {n = suc n} eq (px ∷ all)  = lookupOpt-All eq all

  lookupOpt-app₁ : ∀ (l₁ l₂ : List A) {n} →
                     n < length l₁ →
                     lookupOpt (l₁ ++ l₂) n ≡ lookupOpt l₁ n
  lookupOpt-app₁ [] l₂ {n} ()
  lookupOpt-app₁ (x ∷ l₁) l₂ {zero} (s≤s n<l) = refl
  lookupOpt-app₁ (x ∷ l₁) l₂ {suc n} (s≤s n<l) = lookupOpt-app₁ l₁ l₂ n<l

  lookupOpt-app₂ : ∀ (l₁ l₂ : List A) n →
                     lookupOpt (l₁ ++ l₂) (length l₁ + n) ≡ lookupOpt l₂ n
  lookupOpt-app₂ [] l₂ n       = refl
  lookupOpt-app₂ (x ∷ l₁) l₂ n = lookupOpt-app₂ l₁ l₂ n

repeat : ∀ {a} {A : Set a} → ℕ → (f : A → A) → A → A
repeat zero f = id
repeat (suc n) f = f ∘ (repeat n f)

≤?-yes : ∀ {m n} (m≤n : m ≤ n) → (m ≤? n) ≡ yes m≤n
≤?-yes z≤n           = refl
≤?-yes (s≤s m≤n)
  rewrite ≤?-yes m≤n = refl

≤?-no : ∀ {m n} (m>n : ¬ m ≤ n) → ∃ λ ¬p → (m ≤? n) ≡ no ¬p
≤?-no {m} {n} m>n with m ≤? n
... | yes p = ⊥-elim $ m>n p
... | no _  = -, refl

module Measure {a b ℓ} {A : Set a} {B : Set b} {_≺_ : Rel A ℓ}
               (≺-wf : WellFounded _≺_)
               (m : B → A) where

  open import Level using () renaming (zero to lzero)
  import Relation.Binary.Reasoning.Base.Triple as Triple
  open Wf.Inverse-image {_<_ = _≺_} m using (wellFounded)
  
  open Wf.All (wellFounded ≺-wf) lzero using (wfRec) public

module LexicographicMeasure {a b c d ℓ₁ ℓ₂}
                            {A : Set a} {B : A → Set b}
                            {C : Set c} {D : C → Set d}
                            {_≺A_ : Rel A ℓ₁}
                            {[_]_≺B_ : ∀ x → Rel (B x) ℓ₂}
                            (≺A-wf : WellFounded _≺A_)
                            (≺B-wf : ∀ {x} → WellFounded ([ x ]_≺B_))
                            (mC : C → A)
                            (mD : ∀ {c} → D c → B (mC c)) where
  open import Level using () renaming (zero to lzero)
  module Lex = Wf.Lexicographic _≺A_ [_]_≺B_
  open Lex renaming (wellFounded to lex-wf ; _<_ to _≺′_)
  open Lex using (left ; right) public
  open Wf.Inverse-image renaming (wellFounded to m-wf)

  measure : Σ C D → Σ A B
  measure (c , d) = mC c , mD d

  ΣAB-wf : WellFounded _≺′_
  ΣAB-wf = lex-wf ≺A-wf ≺B-wf

  infix 3 _≺_
  _≺_ = _≺′_ on ,.map mC mD

  measure-wf : WellFounded _≺_
  measure-wf = m-wf measure ΣAB-wf
  
  open Wf.All measure-wf lzero using (wfRec) public
