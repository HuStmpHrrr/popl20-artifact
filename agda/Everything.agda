{-# OPTIONS --without-K --safe #-}

-- The Everything module of undecidability analysis
-- In Agda, we use first order de Bruijn indices to represent variables, that is, the
-- natural numbers.
module Everything where

-- Subtyping problems of all following calculi are undecidable.  In this technical
-- work, our reduction proofs stop at F<: deterministic (F<:ᵈ), the undecidability of
-- which is justified by Pierce92.

-- F<: F<:⁻ F<:ᵈ
import FsubMinus

-- D<:
-- 
-- The examination of D<: is composed of the following files:
import DsubDef -- defines the syntax of D<:.
import Dsub -- defines the simplified subtyping judgment per Lemma 2 in the paper.
import DsubFull -- defines the original definition of D<:.
import DsubEquivSimpler -- defines D<: normal form and shows that D<: subtyping is undecidable.
import DsubNoTrans -- shows that D<: subtyping without transitivity remains undecidable.
import DsubTermUndec -- shows that D<: term typing is also undecidable.

-- other things

-- properties of F<:⁻
import FsubMinus2
