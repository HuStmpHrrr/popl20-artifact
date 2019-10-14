{-# OPTIONS --without-K --safe #-}

-- This module shows that D<: typing is undecidable.
module DsubTermUndec where

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
open import DsubFull
open import DsubReduced
open import Dsub renaming (_⊢_<:_ to _⊢′_<:_)
open import Utils
open import DsubEquivSimpler

module DifferentProof where

  open import FsubMinus
  open FsubMinus.FsubMinus hiding (_↑_)
  open FsubMinusToDsubR
  open Undecidability′

  F<:⇒typing′ : ∀ {Γ S U} →
                  Γ ⊢F S <: U →
                  ⟪ Γ ⟫ ⊢ val ⟨A= ⟦ S ⟧ ⟩ ∶ ⟨A: ⊥ ⋯ ⟦ U ⟧ ⟩
  F<:⇒typing′ S<:U = <∶ ⟨A⟩-I (bnd ⊥<: (<:′⇒<: $ F<:⇒D<: S<:U))

  bnd<:⇒F<:′ : ∀ {Γ S U} →
                  ⟪ Γ ⟫ ⊢″ ⟨A: ⟦ S ⟧ ⋯ ⟦ S ⟧ ⟩ <: ⟨A: ⊥ ⋯ ⟦ U ⟧ ⟩ →
                  Γ ⊢F S <: U
  bnd<:⇒F<:′ {Γ} {S} {U} bnd<: = helper
    where open DsubInvProperties contraInvertible
          cΓ = ⟪⟫-contraEnv Γ
          helper : Γ ⊢F S <: U
          helper with ⟨A:⟩<:⟨A:⟩ (<:⇒<:ᵢ (<:″⇒<: bnd<:) cΓ) cΓ
          ... | _ , S<:U = D<:⇒F<: $ <:ᵢ⇒<: S<:U

  typing⇒F<:′ : ∀ {Γ S U} →
                  ⟪ Γ ⟫ ⊢ val ⟨A= ⟦ S ⟧ ⟩ ∶ ⟨A: ⊥ ⋯ ⟦ U ⟧ ⟩ →
                  Γ ⊢F S <: U
  typing⇒F<:′ typ = bnd<:⇒F<:′ $ <:⇒<:″ $ <:⇒<:′ (helper typ refl refl)
    where helper : ∀ {Γ Γ′ S S′ T} →
                     Γ′ ⊢ val ⟨A= S′ ⟩ ∶ T →
                     Γ′ ≡ ⟪ Γ ⟫ → S′ ≡ ⟦ S ⟧ → 
                     ⟪ Γ ⟫ ⊢ ⟨A: ⟦ S ⟧ ⋯ ⟦ S ⟧ ⟩ <: T
          helper ⟨A⟩-I eqΓ refl = refl
          helper (<∶ typ x) refl eqS = tran _ (helper typ refl eqS) x
