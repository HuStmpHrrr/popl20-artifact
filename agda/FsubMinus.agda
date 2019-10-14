{-# OPTIONS --without-K --safe #-}

-- In this module, we define F<:⁻, F<:ᵈ (F<: deterministic defined in Pierce92) and
-- show that F<:⁻ subtyping is undecidable.
module FsubMinus where

open import Data.List as List
open import Data.Nat
open import Data.Maybe as Maybe
open import Data.Product
open import Data.Vec as Vec renaming (_∷_ to _‼_ ; [] to nil) hiding (_++_)
open import Function
open import Data.Empty renaming (⊥ to False)

open import Relation.Nullary
open import Relation.Unary using () renaming (Decidable to UDecidable)
open import Relation.Binary using () renaming (Decidable to BDecidable)
open import Relation.Binary.PropositionalEquality as ≡

open import Data.Nat.Properties as ℕₚ
open import Data.Maybe.Properties as Maybeₚ
open import Utils

-- Definition of F<:⁻
--
-- F<:⁻ is defined by removing function types (_⟶_ in the paper) from F<:.
module FsubMinus where
  infix 6 var_
  infixr 6 Π<:_∙_

  -- Types
  --
  -- * ⊤ is a supertype of all types.
  -- * (var n) represents a type variable.
  -- * (Π<: S ∙ U) represent a universal type (∀ X <: S . U).
  data Ftyp : Set where
    ⊤       : Ftyp
    var_    : ℕ → Ftyp
    Π<:_∙_  : Ftyp → Ftyp → Ftyp

  -- typing context
  Env : Set
  Env = List Ftyp

  -- shifting operation of de Bruijn indices
  infixl 7 _↑_
  _↑_ : Ftyp → ℕ → Ftyp
  ⊤ ↑ n           = ⊤
  (var x) ↑ n with n ≤? x
  ... | yes p     = var (suc x)
  ... | no ¬p     = var x
  (Π<: S ∙ U) ↑ n = Π<: S ↑ n ∙ U ↑ suc n

  infix 4 _<:_∈_
  data _<:_∈_ : ℕ → Ftyp → Env → Set where
    hd : ∀ {T Γ} → 0 <: T ↑ 0 ∈ T ∷ Γ
    tl : ∀ {n T T′ Γ} → n <: T ∈ Γ → suc n <: T ↑ 0 ∈ T′ ∷ Γ

  -- subtyping judgment of F<:⁻
  -- The statement of the rules should be self-explanatory.
  infix 4 _⊢F_<:_  
  data _⊢F_<:_ : Env → Ftyp → Ftyp → Set where
    ftop   : ∀ {Γ T} →
      Γ ⊢F T <: ⊤
    fvrefl : ∀ {Γ n} →
      Γ ⊢F var n <: var n
    fbinds : ∀ {Γ n T U} →
      n <: T ∈ Γ →
      Γ ⊢F T <: U →
      Γ ⊢F var n <: U
    fall   : ∀ {Γ S₁ S₂ U₁ U₂} →
      Γ ⊢F S₂ <: S₁ →
      Γ ‣ S₂ ! ⊢F U₁ <: U₂ →
      Γ ⊢F Π<: S₁ ∙ U₁ <: Π<: S₂ ∙ U₂

  -- The remaining are some technical setup.
  env-lookup : Env → ℕ → Maybe Ftyp
  env-lookup [] n = nothing
  env-lookup (T ∷ Γ) zero = just $ T ↑ 0
  env-lookup (T ∷ Γ) (suc n) = Maybe.map (_↑ 0) $ env-lookup Γ n

  lookup⇒<:∈ : ∀ {Γ n T} → env-lookup Γ n ≡ just T → n <: T ∈ Γ
  lookup⇒<:∈ {[]} {n} ()
  lookup⇒<:∈ {T ∷ Γ} {zero} refl = hd
  lookup⇒<:∈ {T ∷ Γ} {suc n} eq with env-lookup Γ n | lookup⇒<:∈ {Γ} {n}
  ... | nothing | rec with eq
  ... | ()
  lookup⇒<:∈ {T ∷ Γ} {suc n} refl | just T′ | rec = tl (rec refl) 

  <:∈⇒lookup : ∀ {Γ n T} → n <: T ∈ Γ → env-lookup Γ n ≡ just T
  <:∈⇒lookup hd            = refl
  <:∈⇒lookup (tl <:∈)
    rewrite <:∈⇒lookup <:∈ = refl

  env-lookup′ : Env → ℕ → Maybe Ftyp
  env-lookup′ Γ n = Maybe.map (repeat (suc n) (_↑ 0)) (lookupOpt Γ n)

  env-lookup-same : ∀ Γ n → env-lookup Γ n ≡ env-lookup′ Γ n
  env-lookup-same [] n          = refl
  env-lookup-same (T ∷ Γ) zero  = refl
  env-lookup-same (T ∷ Γ) (suc n)
    rewrite env-lookup-same Γ n = sym $ Maybeₚ.map-compose (lookupOpt Γ n)

  <:∈-map : ∀ {a} {A : Set a} {n T} {f : A → Ftyp} {_↑′_ : A → ℕ → A} Γ →
              (∀ a n → f a ↑ n ≡ f (a ↑′ n)) →
              n <: T ∈ List.map f Γ → ∃ λ a → T ≡ f a
  <:∈-map {f = f} Γ comm d = aux _ d refl
    where aux : ∀ {n T Γ*} Γ → n <: T ∈ Γ* → Γ* ≡ List.map f Γ → ∃ λ a → T ≡ f a
          aux [] hd ()
          aux (T ∷ Γ) hd refl = -, comm _ _
          aux [] (tl <:∈) ()
          aux (T ∷ Γ) (tl <:∈) refl with aux Γ <:∈ refl
          ... | a , refl      = -, comm _ _

  <:∈-func : ∀ {x T T′ Γ} → x <: T ∈ Γ → x <: T′ ∈ Γ → T ≡ T′
  <:∈-func hd hd              = refl
  <:∈-func (tl T∈Γ) (tl T′∈Γ) = cong (_↑ 0) (<:∈-func T∈Γ T′∈Γ)

  Ftyp-measure : Ftyp → ℕ
  Ftyp-measure ⊤           = 1
  Ftyp-measure (var x)     = 1
  Ftyp-measure (Π<: S ∙ U) = Ftyp-measure S + Ftyp-measure U

  Ftyp-measure≥1 : ∀ T → Ftyp-measure T ≥ 1
  Ftyp-measure≥1 ⊤           = s≤s z≤n
  Ftyp-measure≥1 (var _)     = s≤s z≤n
  Ftyp-measure≥1 (Π<: S ∙ U) = ≤-trans (Ftyp-measure≥1 S) (≤-stepsʳ _ ≤-refl)

  ↑-idx : ℕ → ℕ → ℕ
  ↑-idx x n with n ≤? x
  ... | yes p = suc x
  ... | no ¬p = x
  
  ↑-var : ∀ x n → (var x) ↑ n ≡ var (↑-idx x n)
  ↑-var x n with n ≤? x
  ... | yes p = refl
  ... | no ¬p = refl
  
  Ftyp-measure-↑ : ∀ T m → Ftyp-measure (T ↑ m) ≡ Ftyp-measure T
  Ftyp-measure-↑ ⊤ m                 = refl
  Ftyp-measure-↑ (var x) m
    rewrite ↑-var x m                = refl
  Ftyp-measure-↑ (Π<: S ∙ U) m
    rewrite Ftyp-measure-↑ S m
          | Ftyp-measure-↑ U (suc m) = refl

  F-measure : ∀ {Γ S U} → Γ ⊢F S <: U → ℕ
  F-measure ftop         = 1
  F-measure fvrefl       = 1
  F-measure (fbinds _ D) = 1 + F-measure D
  F-measure (fall D₁ D₂) = 1 + F-measure D₁ + F-measure D₂

  F-deriv = Σ (Env × Ftyp × Ftyp) λ { (Γ , S , U) → Γ ⊢F S <: U }

  env : F-deriv → Env
  env ((Γ , _) , _) = Γ

  typ₁ : F-deriv → Ftyp
  typ₁ ((_ , S , U) , _) = S

  typ₂ : F-deriv → Ftyp
  typ₂ ((_ , S , U) , _) = U

  F-measure-packed : F-deriv → ℕ
  F-measure-packed (_ , D) = F-measure D

  ≡⊤-dec : UDecidable (_≡ ⊤)
  ≡⊤-dec ⊤           = yes refl
  ≡⊤-dec (var _)     = no (λ ())
  ≡⊤-dec (Π<: _ ∙ _) = no (λ ())
  
  Π<:-injective : ∀ {S U S′ U′} → Π<: S ∙ U ≡ Π<: S′ ∙ U′ → S ≡ S′ × U ≡ U′
  Π<:-injective refl = refl , refl
  
  Ftyp-≡-dec : BDecidable (_≡_ {A = Ftyp})
  Ftyp-≡-dec ⊤ ⊤                  = yes refl
  Ftyp-≡-dec ⊤ (var _)            = no (λ ())
  Ftyp-≡-dec ⊤ (Π<: _ ∙ _)        = no (λ ())
  Ftyp-≡-dec (var _) ⊤            = no (λ ())
  Ftyp-≡-dec (var x) (var y) with x ≟ y
  ... | yes x≡y                   = yes (cong var_ x≡y)
  ... | no x≢y                    = no (λ { refl → x≢y refl })
  Ftyp-≡-dec (var _) (Π<: _ ∙ _)  = no (λ ())
  Ftyp-≡-dec (Π<: _ ∙ _) ⊤        = no (λ ())
  Ftyp-≡-dec (Π<: _ ∙ _) (var _)  = no (λ ())
  Ftyp-≡-dec (Π<: S ∙ U) (Π<: S′ ∙ U′)
    with Ftyp-≡-dec S S′ | Ftyp-≡-dec U U′
  ... | yes S≡S′ | yes U≡U′       = yes (cong₂ Π<:_∙_ S≡S′ U≡U′)
  ... | yes S≡S′ | no U≢U′        = no λ Π<:≡ → U≢U′ (proj₂ (Π<:-injective Π<:≡))
  ... | no S≢S′  | yes U≡U′       = no (λ Π<:≡ → S≢S′ (proj₁ (Π<:-injective Π<:≡)))
  ... | no S≢S′  | no U≢U′        = no (λ Π<:≡ → S≢S′ (proj₁ (Π<:-injective Π<:≡)))

-- Definition of F<:
--
-- Here we also define full F<:. We do not use it anywhere.
module Full where

  infix 6 var_
  infixr 6 _⇒_ Π<:_∙_
  
  -- Types
  --
  -- * ⊤ is a supertype of all types.
  -- * (var n) represent a type variable.
  -- * (S ⇒ U) represents a function type (S ⟶ U).
  -- * (Π<: S ∙ U) represents a universal type (∀ X <: S . U).
  data Ftyp : Set where
    ⊤       : Ftyp
    var_    : ℕ → Ftyp
    _⇒_     : Ftyp → Ftyp → Ftyp
    Π<:_∙_  : Ftyp → Ftyp → Ftyp
  
  Env : Set
  Env = List Ftyp

  infixl 7 _↑_
  _↑_ : Ftyp → ℕ → Ftyp
  ⊤ ↑ n           = ⊤
  (var x) ↑ n with n ≤? x
  ... | yes p     = var (suc x)
  ... | no ¬p     = var x
  (S ⇒ U) ↑ n     = S ↑ n ⇒ U ↑ n
  (Π<: S ∙ U) ↑ n = Π<: S ↑ n ∙ U ↑ suc n

  infix 4 _<:_∈_
  data _<:_∈_ : ℕ → Ftyp → Env → Set where
    hd : ∀ {T Γ} → 0 <: T ↑ 0 ∈ T ∷ Γ
    tl : ∀ {n T T′ Γ} → n <: T ∈ Γ → suc n <: T ↑ 0 ∈ T′ ∷ Γ

  infix 4 _⊢F_<:_
  
  data _⊢F_<:_ : Env → Ftyp → Ftyp → Set where
    ftop   : ∀ {Γ T} → Γ ⊢F T <: ⊤
    fvrefl : ∀ {Γ n} → Γ ⊢F var n <: var n
    fbinds : ∀ {Γ n T U} →
               n <: T ∈ Γ →
               Γ ⊢F T <: U →
               Γ ⊢F var n <: U
    ffun   : ∀ {Γ S₁ S₂ U₁ U₂} →
               Γ ⊢F S₂ <: S₁ →
               Γ ⊢F U₁ <: U₂ →
               Γ ⊢F S₁ ⇒ U₁ <: S₂ ⇒ U₂
    fall   : ∀ {Γ S₁ S₂ U₁ U₂} →
               Γ ⊢F S₂ <: S₁ →
               S₂ ∷ Γ ⊢F U₁ <: U₂ →
               Γ ⊢F Π<: S₁ ∙ U₁ <: Π<: S₂ ∙ U₂
  
  env-lookup : Env → ℕ → Maybe Ftyp
  env-lookup [] n = nothing
  env-lookup (T ∷ Γ) zero = just $ T ↑ 0
  env-lookup (T ∷ Γ) (suc n) = Maybe.map (_↑ 0) $ env-lookup Γ n

  lookup⇒<:∈ : ∀ {Γ n T} → env-lookup Γ n ≡ just T → n <: T ∈ Γ
  lookup⇒<:∈ {[]} {n} ()
  lookup⇒<:∈ {T ∷ Γ} {zero} refl = hd
  lookup⇒<:∈ {T ∷ Γ} {suc n} eq with env-lookup Γ n | lookup⇒<:∈ {Γ} {n}
  ... | nothing | rec with eq
  ... | ()
  lookup⇒<:∈ {T ∷ Γ} {suc n} refl | just T′ | rec = tl (rec refl) 

  <:∈⇒lookup : ∀ {Γ n T} → n <: T ∈ Γ → env-lookup Γ n ≡ just T
  <:∈⇒lookup hd            = refl
  <:∈⇒lookup (tl <:∈)
    rewrite <:∈⇒lookup <:∈ = refl

  env-lookup′ : Env → ℕ → Maybe Ftyp
  env-lookup′ Γ n = Maybe.map (repeat (suc n) (_↑ 0)) (lookupOpt Γ n)

  env-lookup-same : ∀ Γ n → env-lookup Γ n ≡ env-lookup′ Γ n
  env-lookup-same [] n          = refl
  env-lookup-same (T ∷ Γ) zero  = refl
  env-lookup-same (T ∷ Γ) (suc n)
    rewrite env-lookup-same Γ n = sym $ Maybeₚ.map-compose (lookupOpt Γ n)

open FsubMinus

-- Undecidability of F<:
--
-- Here we show a reduction proof from F<:⁻ to F<:. Assuming F<:⁻ subtyping being
-- undecidable (which is about to be shown below), we formalize that F<: subtyping is
-- undecidable.
module FsubUndec where

  -- the interpretation function of types from F<:⁻ to F<:
  infixl 5 _*  
  _* : Ftyp → Full.Ftyp
  ⊤ *           = Full.⊤
  var x *       = Full.var x
  Π<: T₁ ∙ T₂ * = Full.Π<: T₁ * ∙ (T₂ *)

  *-↑-comm : ∀ (T : Ftyp) n → (T *) Full.↑ n ≡ (T ↑ n) *
  *-↑-comm ⊤ n = refl
  *-↑-comm (var x) n with n ≤? x
  ... | yes p  = refl
  ... | no ¬p  = refl
  *-↑-comm (Π<: S ∙ U) n rewrite *-↑-comm S n | *-↑-comm U (suc n)
               = refl

  repeat*-↑-comm : ∀ T n m → repeat n (Full._↑ m) (T *) ≡ (repeat n (_↑ m) T) *
  repeat*-↑-comm T zero m        = refl
  repeat*-↑-comm T (suc n) m
    rewrite repeat*-↑-comm T n m = *-↑-comm (repeat n (_↑ m) T) m

  *-injective : ∀ {S U} → S * ≡ U * → S ≡ U
  *-injective {⊤} {⊤} refl            = refl
  *-injective {⊤} {var x} ()
  *-injective {⊤} {Π<: _ ∙ _} ()
  *-injective {var x} {⊤} ()
  *-injective {var x} {var .x} refl   = refl
  *-injective {var _} {Π<: _ ∙ _} ()
  *-injective {Π<: S ∙ S₁} {⊤} ()
  *-injective {Π<: _ ∙ _} {var x} ()
  *-injective {Π<: S ∙ S₁} {Π<: U ∙ U₁} eq
    with S * | U * | *-injective {S} {U} | S₁ * | U₁ * | *-injective {S₁} {U₁}
  ... | S* | U* | r | S₁* | U₁* | r₁ with eq
  ... | refl rewrite r refl | r₁ refl = refl

  Full<:∈⇒<:∈ : ∀ {Γ n T} → n Full.<: T * ∈ List.map _* Γ → n <: T ∈ Γ
  Full<:∈⇒<:∈ {Γ} {n} <:∈
    with Full.<:∈⇒lookup <:∈
  ...  | eq rewrite Full.env-lookup-same (List.map _* Γ) n
    with lookupOpt (List.map _* Γ) n | lookupOpt-map-inv {f = _*} Γ {n}
  ...  | just T  | inv
       with inv refl
  ...     | T′ , refl , lk
          with just-injective eq
  ...        | eq′
    rewrite repeat*-↑-comm T′ n 0 | *-↑-comm (repeat n (_↑ 0) T′) 0
    with *-injective eq′
  ...  | refl = lookup⇒<:∈ (trans (env-lookup-same Γ n) aux)
    where aux : env-lookup′ Γ n ≡ just (repeat n (_↑ 0) T′ ↑ 0)
          aux rewrite lk = refl
  Full<:∈⇒<:∈ {Γ} {n} <:∈ | () | nothing | _ 

  <:∈⇒Full<:∈ : ∀ {Γ n T} → n <: T ∈ Γ → n Full.<: T * ∈ List.map _* Γ
  <:∈⇒Full<:∈ (hd {T})
    rewrite sym $ *-↑-comm T 0 = Full.hd
  <:∈⇒Full<:∈ (tl {T = T} <:∈)
    rewrite sym $ *-↑-comm T 0 = Full.tl (<:∈⇒Full<:∈ <:∈)

  full⇒minus-gen : ∀ {Γ* S* U*} → Γ* Full.⊢F S* <: U* →
               ∀ {Γ S U} → Γ* ≡ List.map _* Γ → S* ≡ (S *) → U* ≡ (U *) →
                 Γ ⊢F S <: U
  full⇒minus-gen Full.ftop {Γ} {S} {⊤} eqΓ eqS refl             = ftop
  full⇒minus-gen Full.ftop {Γ} {S} {var x} eqΓ eqS ()
  full⇒minus-gen Full.ftop {Γ} {S} {Π<: U ∙ U₁} eqΓ eqS ()
  full⇒minus-gen Full.fvrefl {Γ} {⊤} {⊤} eqΓ () eqU
  full⇒minus-gen Full.fvrefl {Γ} {var x} {⊤} eqΓ refl ()
  full⇒minus-gen Full.fvrefl {Γ} {Π<: S ∙ S₁} {⊤} eqΓ () eqU
  full⇒minus-gen Full.fvrefl {Γ} {⊤} {var x} eqΓ () eqU
  full⇒minus-gen Full.fvrefl {Γ} {var x} {var .x} eqΓ refl refl = fvrefl
  full⇒minus-gen Full.fvrefl {Γ} {Π<: S ∙ S₁} {var x} eqΓ () eqU
  full⇒minus-gen Full.fvrefl {Γ} {⊤} {Π<: U ∙ U₁} eqΓ () eqU
  full⇒minus-gen Full.fvrefl {Γ} {var x} {Π<: U ∙ U₁} eqΓ refl ()
  full⇒minus-gen Full.fvrefl {Γ} {Π<: S ∙ S₁} {Π<: U ∙ U₁} eqΓ () eqU
  full⇒minus-gen (Full.fbinds T∈Γ* Dfull) {Γ} {⊤} {U} eqΓ () eqU
  full⇒minus-gen (Full.fbinds {n = n} T∈Γ* Dfull)
             {Γ} {var x} {U} eqΓ refl eqU       = aux
    where T′∈Γ : ∀ {Γ* T} → n Full.<: T ∈ Γ* → Γ* ≡ List.map _* Γ → ∃[ T′ ] (T ≡ T′ *)
          T′∈Γ <:∈ refl with Full.<:∈⇒lookup <:∈
          ... | eq rewrite Full.env-lookup-same (List.map _* Γ) n
            with lookupOpt (List.map _* Γ) n | inspect (lookupOpt (List.map _* Γ)) n
          ... | just T | [ lk ]
            with lookupOpt-map-inv Γ lk | just-injective eq
          ... | T′ , refl , lkeq | eq′
            rewrite repeat*-↑-comm T′ n 0
              | *-↑-comm (repeat n (_↑ 0) T′) 0 = -, sym eq′
          T′∈Γ <:∈ refl | () | nothing | _
          aux : Γ ⊢F var n <: U
          aux with T′∈Γ T∈Γ* eqΓ
          ... | T′ , refl rewrite eqΓ           = fbinds (Full<:∈⇒<:∈ T∈Γ*) (full⇒minus-gen Dfull refl refl eqU)
  full⇒minus-gen (Full.fbinds T∈Γ* Dfull) {Γ} {Π<: S ∙ S₁} {U} eqΓ () eqU
  full⇒minus-gen (Full.ffun _ _) {Γ} {⊤} {U} eqΓ () eqU
  full⇒minus-gen (Full.ffun _ _) {Γ} {var x₂} {U} eqΓ () eqU
  full⇒minus-gen (Full.ffun _ _) {Γ} {Π<: S ∙ S₁} {U} eqΓ () eqU
  full⇒minus-gen (Full.fall Dp Dbody) {Γ} {⊤} {⊤} eqΓ () eqU
  full⇒minus-gen (Full.fall Dp Dbody) {Γ} {⊤} {var x} eqΓ () eqU
  full⇒minus-gen (Full.fall Dp Dbody) {Γ} {⊤} {Π<: U ∙ U₁} eqΓ () eqU
  full⇒minus-gen (Full.fall Dp Dbody) {Γ} {var x} {⊤} eqΓ () eqU
  full⇒minus-gen (Full.fall Dp Dbody) {Γ} {var x} {var x₁} eqΓ () eqU
  full⇒minus-gen (Full.fall Dp Dbody) {Γ} {var x} {Π<: U ∙ U₁} eqΓ () eqU
  full⇒minus-gen (Full.fall Dp Dbody) {Γ} {Π<: S ∙ S₁} {⊤} eqΓ refl ()
  full⇒minus-gen (Full.fall Dp Dbody) {Γ} {Π<: S ∙ S₁} {var x} eqΓ refl ()
  full⇒minus-gen (Full.fall Dp Dbody) {Γ} {Π<: S₁ ∙ U₁} {Π<: S₂ ∙ U₂}
                 eqΓ refl refl = fall (full⇒minus-gen Dp eqΓ refl refl)
                                      (full⇒minus-gen Dbody (aux eqΓ) refl refl)
    where aux : ∀ {Γ*} → Γ* ≡ List.map _* Γ → (S₂ *) ∷ Γ* ≡ (S₂ *) ∷ List.map _* Γ
          aux refl             = refl

  -- The following two functions accomplish the reduction proof.
  full⇒minus : ∀ {Γ S U} → List.map _* Γ Full.⊢F S * <: U * → Γ ⊢F S <: U
  full⇒minus Dfull = full⇒minus-gen Dfull refl refl refl
  
  minus⇒full : ∀ {Γ S U} → Γ ⊢F S <: U → List.map _* Γ Full.⊢F S * <: U *
  minus⇒full ftop                    = Full.ftop
  minus⇒full fvrefl                  = Full.fvrefl
  minus⇒full {Γ} (fbinds T∈Γ Dminus) = Full.fbinds (<:∈⇒Full<:∈ T∈Γ) (minus⇒full Dminus)
  minus⇒full (fall Dp Db)            = Full.fall (minus⇒full Dp) (minus⇒full Db)

-- Definition of F<:ᵈ
--
-- Definition of F<:ᵈ F<:ᵈ (F<: deterministic) is an intermediate construction in
-- Pierce92 towards the undecidability proof of F<: subtyping. This intermediate
-- construction is also shown undecidable and we directly use that result here.
module DeterministicFsubSized where

  open import Induction.Nat
  import Relation.Binary.EqReasoning as Eq

  infix 6 var⁻_
  infixr 6 Π⁺<:_∙¬_ Π⁻<:⊤∙¬_

  -- Types
  --
  -- Types in F<:ᵈ are divided into two parts and the two parts are mutually defined.
  -- The two parts are positive types [Ftyp⁺] and negative types [Ftyp⁻] and defined
  -- as follows.
  mutual
  -- Positive types
  -- * ⊤⁺ corresponds to ⊤ in F<:⁻.
  -- * (Π⁺<: Ts ∙¬ U) represents a universal type where all types involved are negative types (∀ X₁ <: T₁ ... ∀ Xₙ <: Tₙ . ∀ X <: U . X).
    data Ftyp⁺ (n : ℕ) : Set where
      ⊤⁺       : Ftyp⁺ n
      Π⁺<:_∙¬_ : Vec (Ftyp⁻ n) n → Ftyp⁻ n → Ftyp⁺ n
  
  -- Negative types
  -- * (var⁻ n) corresponds to a type variable in F<:⁻.
  -- * (Π⁻<:⊤∙¬_ T) represents a universal type where all parameter types are ⊤ and T is positive (∀ X₁ <: ⊤ ... ∀ Xₙ <: ⊤ . ∀ X <: T . X).
    data Ftyp⁻ (n : ℕ) : Set where
      var⁻_    : ℕ → Ftyp⁻ n
      Π⁻<:⊤∙¬_ : Ftyp⁺ n → Ftyp⁻ n

  -- shifting operation for both positive and negative types
  infixl 7 _↑⁺_ _↑⁺_ ⟦_↑⁻_⟧
  mutual
    _↑⁺_ : ∀ {n} → Ftyp⁺ n → ℕ → Ftyp⁺ n
    ⊤⁺ ↑⁺ n                  = ⊤⁺
    _↑⁺_ {m} (Π⁺<: S ∙¬ U) n = Π⁺<: ⟦ S ↑⁻ n ⟧ ∙¬ (U ↑⁻ (m + n))

    _↑⁻_ : ∀ {n} → Ftyp⁻ n → ℕ → Ftyp⁻ n
    (var⁻ x) ↑⁻ n with n ≤? x
    ... | yes p            = var⁻ (suc x)
    ... | no ¬p            = var⁻ x
    _↑⁻_ {m} (Π⁻<:⊤∙¬ T) n = Π⁻<:⊤∙¬ (T ↑⁺ (m + n))

    ⟦_↑⁻_⟧ : ∀ {n m} → Vec (Ftyp⁻ n) m → ℕ → Vec (Ftyp⁻ n) m
    ⟦ nil ↑⁻ n ⟧   = nil
    ⟦ T ‼ S ↑⁻ n ⟧ = T ↑⁻ n ‼ ⟦ S ↑⁻ suc n ⟧ 

  -- In F<:ᵈ, typing contexts consist only of negative types.
  NEnv : ℕ → Set
  NEnv n = List (Ftyp⁻ n)

  nenv-lookup : ∀ {n} → NEnv n → ℕ → Maybe (Ftyp⁻ n)
  nenv-lookup Γ n = Maybe.map (repeat (suc n) (_↑⁻ 0)) (lookupOpt Γ n)

  -- subtyping judgment of F<:ᵈ
  --
  -- For a fixed n, a subtyping judgment of F<:ᵈ is a ternary predicate, among a
  -- typing context (consisting of negative types), a negative type and a positive
  -- type.  A subtyping judgment in F<:ᵈ asserts that a negative type is a subtype of
  -- a positive type in the given context. Notice that there is no subtyping relation
  -- between two negative types or two positive types.
  infix 4 [_]_⊢FD_<:_  
  data [_]_⊢FD_<:_ (n : ℕ) : NEnv n → Ftyp⁻ n → Ftyp⁺ n → Set where
    fdtop : ∀ {Γ T} → [ n ] Γ ⊢FD T <: ⊤⁺
    fdvar : ∀ {Γ m T S U} →
              nenv-lookup Γ m ≡ just T →
              [ n ] Γ ⊢FD T <: Π⁺<: S ∙¬ U → 
              [ n ] Γ ⊢FD var⁻ m <: Π⁺<: S ∙¬ U
    fdall : ∀ {Γ T S U} →
              [ n ] Vec.foldl (λ _ → _) (flip _∷_) Γ S ⊢FD U <: T →
              [ n ] Γ ⊢FD Π⁻<:⊤∙¬ T <: Π⁺<: S ∙¬ U
  
  infix 5 _*⁺ _*⁻
  infix 6 Π⁻[_]∙_ Π⁺_∙_

  -- the interpretation function of types from F<:ᵈ to F<:⁻
  mutual
    _*⁺ : ∀ {n} → Ftyp⁺ n → Ftyp
    ⊤⁺ *⁺         = ⊤
    Π⁺<: S ∙¬ U *⁺ = Π⁻[ S ]∙ U

    Π⁻[_]∙_ : ∀ {n m} → Vec (Ftyp⁻ n) m → Ftyp⁻ n → Ftyp
    Π⁻[ nil ]∙ U    = Π<: U *⁻ ∙ var zero
    Π⁻[ S ‼ Ss ]∙ U = Π<: S *⁻ ∙ Π⁻[ Ss ]∙ U
  
    _*⁻ : ∀ {n} → Ftyp⁻ n → Ftyp
    var⁻ n *⁻          = var n
    _*⁻ {n} (Π⁻<:⊤∙¬ T) = Π⁺ n ∙ T
    
    Π⁺_∙_ : ∀ {n} → ℕ → Ftyp⁺ n → Ftyp
    Π⁺ zero ∙ T  = Π<: T *⁺ ∙ var zero
    Π⁺ suc n ∙ T = Π<: ⊤ ∙ Π⁺ n ∙ T

  module _ where
    open Eq (setoid ℕ)
    
    mutual
      *-↑-comm⁺ : ∀ {m} (T : Ftyp⁺ m) n → (T *⁺) ↑ n ≡ (T ↑⁺ n) *⁺
      *-↑-comm⁺ ⊤⁺ n            = refl
      *-↑-comm⁺ (Π⁺<: S ∙¬ U) n = Π-↑-comm⁻ S U n
  
      Π-↑-comm⁻ : ∀ {i j} (S : Vec (Ftyp⁻ i) j) (U : Ftyp⁻ i) n →
                    (Π⁻[ S ]∙ U) ↑ n ≡ Π⁻[ ⟦ S ↑⁻ n ⟧ ]∙ (U ↑⁻ (j + n))
      Π-↑-comm⁻ nil U n
        rewrite *-↑-comm⁻ U n = refl
      Π-↑-comm⁻ {j = suc j} (T ‼ S) U n
        rewrite *-↑-comm⁻ T n
              | Π-↑-comm⁻ S U (suc n)
              | +-suc j n     = refl
  
      *-↑-comm⁻ : ∀ {m} (T : Ftyp⁻ m) n → (T *⁻) ↑ n ≡ (T ↑⁻ n) *⁻
      *-↑-comm⁻ (var⁻ x) n with n ≤? x
      ... | yes p             = refl
      ... | no ¬p             = refl
      *-↑-comm⁻ (Π⁻<:⊤∙¬ T) n = Π-↑-comm⁺ _ T n

      Π-↑-comm⁺ : ∀ {i} j (T : Ftyp⁺ i) n →
                    (Π⁺ j ∙ T) ↑ n ≡ Π⁺ j ∙ (T ↑⁺ (j + n))
      Π-↑-comm⁺ zero T n
        rewrite *-↑-comm⁺ T n = refl
      Π-↑-comm⁺ (suc j) T n
        rewrite Π-↑-comm⁺ j T (suc n)
              | +-suc j n     = refl

  repeat*-↑-comm⁻ : ∀ {i} (T : Ftyp⁻ i) n m →
                      repeat n (_↑ m) (T *⁻) ≡ (repeat n (_↑⁻ m) T) *⁻
  repeat*-↑-comm⁻ T zero m        = refl
  repeat*-↑-comm⁻ T (suc n) m 
    rewrite repeat*-↑-comm⁻ T n m = *-↑-comm⁻ (repeat n (_↑⁻ m) T) m

  mutual
    *-injective⁺ : ∀ {n} {S U : Ftyp⁺ n} → S *⁺ ≡ U *⁺ → S ≡ U
    *-injective⁺ {n} {⊤⁺} {⊤⁺} eq = refl
    *-injective⁺ {.0} {⊤⁺} {Π⁺<: nil ∙¬ _} ()
    *-injective⁺ {.(suc _)} {⊤⁺} {Π⁺<: _ ‼ _ ∙¬ _} ()
    *-injective⁺ {n} {Π⁺<: S ∙¬ U} {⊤⁺} eq = ⊥-elim $ aux eq
      where aux : ∀ {n m} {S : Vec (Ftyp⁻ n) m} {U} → ¬ Π⁻[ S ]∙ U ≡ ⊤
            aux {S = nil} ()
            aux {S = _ ‼ S} ()
    *-injective⁺ {n} {Π⁺<: S₁ ∙¬ U₁} {Π⁺<: S₂ ∙¬ U₂} eq with Π-injective⁻ eq
    ... | refl , refl = refl

    Π-injective⁻ : ∀ {n m} {S₁ S₂ : Vec (Ftyp⁻ n) m} {U₁ U₂ : Ftyp⁻ n} →
                     Π⁻[ S₁ ]∙ U₁ ≡ Π⁻[ S₂ ]∙ U₂ →
                     S₁ ≡ S₂ × U₁ ≡ U₂
    Π-injective⁻ {S₁ = nil} {nil} {U₁} {U₂} eq
      with U₁ *⁻ | U₂ *⁻ | *-injective⁻ {S = U₁} {U₂}
    ...  | U₁* | U₂* | rec with eq
    ...  | refl = refl , rec refl
    Π-injective⁻ {S₁ = S ‼ S₁} {S′ ‼ S₂} {U₁} {U₂} eq
      with S *⁻ | S′ *⁻ | Π⁻[ S₁ ]∙ U₁ | Π⁻[ S₂ ]∙ U₂
         | *-injective⁻ {S = S} {S′}
         | Π-injective⁻ {S₁ = S₁} {S₂} {U₁} {U₂}
    ...  | S* | S′* | Π₁ | Π₂ | recS | rec with eq
    ...  | refl with recS refl | rec refl
    ...  | refl | refl , eqU = refl , eqU

    *-injective⁻ : ∀ {n} {S U : Ftyp⁻ n} → S *⁻ ≡ U *⁻ → S ≡ U
    *-injective⁻ {n} {var⁻ x} {var⁻ .x} refl = refl
    *-injective⁻ {zero} {var⁻ _} {Π⁻<:⊤∙¬ _} ()
    *-injective⁻ {suc n} {var⁻ _} {Π⁻<:⊤∙¬ _} ()
    *-injective⁻ {n} {Π⁻<:⊤∙¬ T} {var⁻ x} eq = ⊥-elim $ aux _ eq
      where aux : ∀ {n x} {T : Ftyp⁺ n} m → ¬ Π⁺ m ∙ T ≡ var x
            aux zero ()
            aux (suc m) ()
    *-injective⁻ {n} {Π⁻<:⊤∙¬ T₁} {Π⁻<:⊤∙¬ T₂} eq with Π-injective⁺ n eq
    ... | refl = refl

    Π-injective⁺ : ∀ {n} {T₁ T₂ : Ftyp⁺ n} m →
                     Π⁺ m ∙ T₁ ≡ Π⁺ m ∙ T₂ →
                     T₁ ≡ T₂
    Π-injective⁺ {T₁ = T₁} {T₂} zero eq
      with T₁ *⁺ | T₂ *⁺ | *-injective⁺ {S = T₁} {T₂}
    ...  | T₁* | T₂* | rec with eq
    ...  | refl = rec refl
    Π-injective⁺ {T₁ = T₁} {T₂} (suc m) eq
      with Π⁺ m ∙ T₁ | Π⁺ m ∙ T₂ | Π-injective⁺ {T₁ = T₁} {T₂} m
    ...  | Π₁ | Π₂ | rec with eq
    ...  | refl = rec refl

  data Pi (P Q : Ftyp → Set) : ℕ → Ftyp → Set where
    pzero : ∀ {U} → Q U → Pi P Q zero (Π<: U ∙ var zero)
    psuc  : ∀ {n S T} → P S → Pi P Q n T -> Pi P Q (suc n) (Π<: S ∙ T)

  -- two predicates that capture the images of the interpretation functions
  mutual
    -- Covar captures the image of the interpretation function from positive types to F<:.
    data Covar (n : ℕ) : Ftyp → Set where
      cvtop : Covar n ⊤
      cvΠ   : ∀ {T} → Pi (Contra n) (Contra n) n T → Covar n T

    -- Contra captures the image of the interpretation function from negative types to F<:.
    data Contra (n : ℕ) : Ftyp → Set where
      cnvar : ∀ m → Contra n (var m)
      cnΠ   : ∀ {T} → Pi (⊤ ≡_) (Covar n) n T → Contra n T
  
  infix 5 ⟦_⟧⁺ ⟦_⟧⁻

  -- the inverse functions of the interpretation functions
  mutual
    ⟦_⟧⁺ : ∀ {n T} → Covar n T → Ftyp⁺ n
    ⟦ cvtop ⟧⁺ = ⊤⁺
    ⟦ cvΠ P ⟧⁺ = Π⁺<: ∥ P ∥⁺₁ ∙¬ ∥ P ∥⁺₂

    ∥_∥⁺₁ : ∀ {n m T} → Pi (Contra n) (Contra n) m T → Vec (Ftyp⁻ n) m
    ∥ pzero U ∥⁺₁  = nil
    ∥ psuc S P ∥⁺₁ = ⟦ S ⟧⁻ ‼ ∥ P ∥⁺₁

    ∥_∥⁺₂ : ∀ {n m T} → Pi (Contra n) (Contra n) m T → Ftyp⁻ n
    ∥ pzero U ∥⁺₂  = ⟦ U ⟧⁻
    ∥ psuc S P ∥⁺₂ = ∥ P ∥⁺₂
  
    ⟦_⟧⁻ : ∀ {n T} → Contra n T → Ftyp⁻ n
    ⟦ cnvar m ⟧⁻ = var⁻ m
    ⟦ cnΠ P ⟧⁻   = Π⁻<:⊤∙¬ ∥ P ∥⁻
    
    ∥_∥⁻ : ∀ {n m T} → Pi (⊤ ≡_) (Covar n) m T → Ftyp⁺ n
    ∥ pzero T ∥⁻  = ⟦ T ⟧⁺
    ∥ psuc S P ∥⁻ = ∥ P ∥⁻

  mutual
    ⟦⟧⁺*⁺⇒id : ∀ {n T} (cT : Covar n T) → (⟦ cT ⟧⁺ *⁺) ≡ T
    ⟦⟧⁺*⁺⇒id cvtop   = refl
    ⟦⟧⁺*⁺⇒id (cvΠ P) = ∥∥⁻Π⇒id P

    ∥∥⁻Π⇒id : ∀ {n m T} (P : Pi (Contra n) (Contra n) m T) →
                Π⁻[ ∥ P ∥⁺₁ ]∙ ∥ P ∥⁺₂ ≡ T
    ∥∥⁻Π⇒id (pzero U)
      rewrite ⟦⟧⁻*⁻⇒id U             = refl
    ∥∥⁻Π⇒id (psuc S P)
      rewrite ⟦⟧⁻*⁻⇒id S | ∥∥⁻Π⇒id P = refl

    ⟦⟧⁻*⁻⇒id : ∀ {n T} (cT : Contra n T) → (⟦ cT ⟧⁻ *⁻) ≡ T
    ⟦⟧⁻*⁻⇒id (cnvar m) = refl
    ⟦⟧⁻*⁻⇒id (cnΠ P)   = ∥∥⁺Π⇒id P

    ∥∥⁺Π⇒id : ∀ {n m T} (P : Pi (⊤ ≡_) (Covar n) m T) → Π⁺ m ∙ ∥ P ∥⁻ ≡ T
    ∥∥⁺Π⇒id (pzero U) rewrite ⟦⟧⁺*⁺⇒id U    = refl
    ∥∥⁺Π⇒id (psuc refl P) rewrite ∥∥⁺Π⇒id P = refl
  
  infix 5 *⟦_⟧⁺ *⟦_⟧⁻ *∥_,_∥⁺
  
  mutual
  
    *⟦_⟧⁺ : ∀ {n} (T : Ftyp⁺ n) → Covar n (T *⁺)
    *⟦ ⊤⁺ ⟧⁺          = cvtop
    *⟦ Π⁺<: S ∙¬ U ⟧⁺ = cvΠ *∥ S , U ∥⁺

    *∥_,_∥⁺ : ∀ {n m} (S : Vec (Ftyp⁻ n) m) (U : Ftyp⁻ n) →
              Pi (Contra n) (Contra n) m (Π⁻[ S ]∙ U)
    *∥ nil , U ∥⁺    = pzero *⟦ U ⟧⁻
    *∥ S ‼ Ss , U ∥⁺ = psuc *⟦ S ⟧⁻ *∥ Ss , U ∥⁺
  
    *⟦_⟧⁻ : ∀ {n} (T : Ftyp⁻ n) → Contra n (T *⁻)
    *⟦ var⁻ x ⟧⁻    = cnvar x
    *⟦ Π⁻<:⊤∙¬ T ⟧⁻ = cnΠ *∥ _ , T ∥⁻

    *∥_,_∥⁻ : ∀ {n} m (T : Ftyp⁺ n) → Pi (⊤ ≡_) (Covar n) m (Π⁺ m ∙ T)
    *∥ zero , T ∥⁻  = pzero *⟦ T ⟧⁺
    *∥ suc m , T ∥⁻ = psuc refl *∥ m , T ∥⁻
  
  mutual
    *⁺⟦⟧⁺⇒id : ∀ {n} (T : Ftyp⁺ n) → ⟦ *⟦ T ⟧⁺ ⟧⁺ ≡ T
    *⁺⟦⟧⁺⇒id ⊤⁺                           = refl
    *⁺⟦⟧⁺⇒id (Π⁺<: S ∙¬ U)
      rewrite *∥∥⁺₁⇒id S U | *∥∥⁺₂⇒id S U = refl

    *∥∥⁺₁⇒id : ∀ {n m} (S : Vec (Ftyp⁻ n) m) (U : Ftyp⁻ n) → ∥ *∥ S , U ∥⁺ ∥⁺₁ ≡ S
    *∥∥⁺₁⇒id nil U                       = refl
    *∥∥⁺₁⇒id (S ‼ Ss) U
      rewrite *⁻⟦⟧⁻⇒id S | *∥∥⁺₁⇒id Ss U = refl

    *∥∥⁺₂⇒id : ∀ {n m} (S : Vec (Ftyp⁻ n) m) (U : Ftyp⁻ n) → ∥ *∥ S , U ∥⁺ ∥⁺₂ ≡ U
    *∥∥⁺₂⇒id nil U      = *⁻⟦⟧⁻⇒id U
    *∥∥⁺₂⇒id (S ‼ Ss) U = *∥∥⁺₂⇒id Ss U

    *⁻⟦⟧⁻⇒id : ∀ {n} (T : Ftyp⁻ n) → ⟦ *⟦ T ⟧⁻ ⟧⁻ ≡ T
    *⁻⟦⟧⁻⇒id (var⁻ x)     = refl
    *⁻⟦⟧⁻⇒id {n} (Π⁻<:⊤∙¬ T)
      rewrite *∥∥⁻⇒id n T = refl

    *∥∥⁻⇒id : ∀ {n} m (T : Ftyp⁺ n) → ∥ *∥ m , T ∥⁻ ∥⁻ ≡ T
    *∥∥⁻⇒id zero T    = *⁺⟦⟧⁺⇒id T
    *∥∥⁻⇒id (suc m) T = *∥∥⁻⇒id m T

  open Measure <-wellFounded F-measure-packed renaming (wfRec to F-rec)

  minus⇒deterministic-gen : ∀ (D : F-deriv) →
                            ∀ n {Γ} (S : Contra n (typ₁ D)) (U : Covar n (typ₂ D)) →
                              env D ≡ List.map _*⁻ Γ → 
                              [ n ] Γ ⊢FD ⟦ S ⟧⁻ <: ⟦ U ⟧⁺
  minus⇒deterministic-gen D = F-rec (λ D → prop D) pf D
    where prop : F-deriv → Set
          prop D = ∀ n {Γ} (S : Contra n (typ₁ D)) (U : Covar n (typ₂ D)) →
                     env D ≡ List.map _*⁻ Γ → 
                     [ n ] Γ ⊢FD ⟦ S ⟧⁻ <: ⟦ U ⟧⁺
          open ≤-Reasoning

          pf : ∀ (D : F-deriv) →
                 (∀ D′ → F-measure-packed D′ < F-measure-packed D → prop D′) → prop D
          pf ((Γ , S* , .⊤) , ftop) rec n S cvtop eq                       = fdtop
          pf ((Γ , S* , .⊤) , ftop) rec n S (cvΠ ()) eq
          pf ((Γ , .(var _) , .(var _)) , fvrefl) rec n S (cvΠ ()) eq
          pf ((Γ , .(var m) , .⊤) , fbinds T∈Γ D) rec n (cnvar m) cvtop eq = fdtop
          
          pf ((Γ , .(var m) , U*) , fbinds T∈Γ D) rec n {Γ′} (cnvar m) (cvΠ P) refl
            with trans (sym $ env-lookup-same (List.map _*⁻ Γ′) m) $ <:∈⇒lookup T∈Γ
          ... | eq with lookupOpt (List.map _*⁻ Γ′) m | inspect (lookupOpt (List.map _*⁻ Γ′)) m
          pf ((Γ , .(var m) , U*) , fbinds T∈Γ D) rec n {Γ′} (cnvar m) (cvΠ P) refl | refl | just T | [ lk ]
            with lookupOpt-map-inv Γ′ lk
          ...  | T′ , refl , lk′
            rewrite repeat*-↑-comm⁻ T′ m 0
               | *-↑-comm⁻ (repeat m (_↑⁻ 0) T′) 0
            with rec (-, D) ≤-refl n *⟦ repeat m (_↑⁻ 0) T′ ↑⁻ 0 ⟧⁻ (cvΠ P) refl
          ...  | Drec rewrite *⁻⟦⟧⁻⇒id (repeat m (_↑⁻ 0) T′ ↑⁻ 0)
            = fdvar (cong (Maybe.map (repeat (suc m) (_↑⁻ 0))) lk′) Drec
          pf ((Γ , .(var m) , U*) , fbinds T∈Γ D) rec n {Γ′} (cnvar m) (cvΠ P) refl | () | nothing | [ lk ]

          pf ((Γ , .(var _) , U*) , fbinds T∈Γ D) rec n (cnΠ ()) U eq
          pf ((Γ , .(Π<: _ ∙ _) , .(Π<: _ ∙ _)) , Dtop@(fall S₂<:S₁ U₁<:U₂))
             rec n (cnΠ Ps) (cvΠ Pu) refl                                  = fdall (aux _ n (fall S₂<:S₁ U₁<:U₂) Ps Pu ≤-refl)
            where transport : ∀ {Γ T₁ T₂ S*} (S : Contra n S*)
                                (D : S* ∷ Γ ⊢F T₁ <: T₂) →
                                Σ ((⟦ S ⟧⁻ *⁻) ∷ Γ ⊢F T₁ <: T₂) (λ D′ → F-measure D′ ≡ F-measure D)
                  transport {Γ} {T₁} {T₂} S D
                    = subst (λ S → Σ (S ∷ Γ ⊢F T₁ <: T₂) (λ D′ → F-measure D′ ≡ F-measure D))
                            (sym $ ⟦⟧⁻*⁻⇒id S) (D , refl)

                  aux : ∀ {T₁ T₂} Γ m (D : List.map _*⁻ Γ ⊢F T₁ <: T₂)
                          (Ps : Pi (_≡_ ⊤) (Covar n) m T₁)
                          (Pu : Pi (Contra n) (Contra n) m T₂) →
                          F-measure D ≤ F-measure Dtop →
                          [ n ] Vec.foldl (λ _ → _) (flip _∷_) Γ ∥ Pu ∥⁺₁ ⊢FD ∥ Pu ∥⁺₂ <: ∥ Ps ∥⁻
                  aux Γ zero (fall <:₁ <:₂) (pzero S₁) (pzero S₂) ≤
                    = rec (-, <:₁) (≤-trans shrinks ≤) n S₂ S₁ refl
                    where shrinks : (F-measure <:₁) < suc (F-measure <:₁ + F-measure <:₂)
                          shrinks = begin-strict
                            F-measure <:₁                       ≤⟨ ≤-stepsʳ (F-measure <:₂) ≤-refl ⟩
                            F-measure <:₁ + F-measure <:₂       <⟨ ≤-refl ⟩
                            suc (F-measure <:₁ + F-measure <:₂) ∎
                  aux Γ (suc m) (fall <:₁ <:₂) (psuc refl Ps) (psuc S₂ Pu) ≤
                    with transport S₂ <:₂
                  ... | <:₂′ , eq = aux (⟦ S₂ ⟧⁻ ∷ Γ) m <:₂′ Ps Pu $
                    begin
                      F-measure <:₂′                            ≡⟨ eq ⟩
                      F-measure <:₂                             ≤⟨ ≤-stepsˡ (F-measure <:₁) ≤-refl ⟩
                      F-measure <:₁ + F-measure <:₂             <⟨ ≤ ⟩
                      suc (F-measure S₂<:S₁ + F-measure U₁<:U₂) ∎

  -- The following two functions conclude the reduction proof from F<:ᵈ to F<:⁻.
  minus⇒deterministic : ∀ n {Γ : NEnv n} {S U} → List.map _*⁻ Γ ⊢F S *⁻ <: U *⁺ → [ n ] Γ ⊢FD S <: U
  minus⇒deterministic n {Γ} {S} {U} D with minus⇒deterministic-gen (-, D) n *⟦ S ⟧⁻ *⟦ U ⟧⁺ refl
  ... | D′ rewrite *⁻⟦⟧⁻⇒id S | *⁺⟦⟧⁺⇒id U = D′

  deterministic⇒minus : ∀ n {Γ : NEnv n} {S U} → [ n ] Γ ⊢FD S <: U → List.map _*⁻ Γ ⊢F S *⁻ <: U *⁺
  deterministic⇒minus n fdtop             = ftop
  deterministic⇒minus n {Γ} (fdvar {m = m} T∈Γ D)
    with lookupOpt Γ m | inspect (lookupOpt Γ) m
  deterministic⇒minus n {Γ} (fdvar {m = m} refl D) | just T | [ eq ]
    = fbinds (lookup⇒<:∈ $ begin
                env-lookup (List.map _*⁻ Γ) m       ≡⟨ env-lookup-same (List.map _*⁻ Γ) m ⟩
                env-lookup′ (List.map _*⁻ Γ) m      ≡⟨ cong (Maybe.map (repeat (suc m) (_↑ 0)))
                                                            (lookupOpt-map Γ _*⁻ eq) ⟩
                just (repeat m (_↑ 0) (T *⁻) ↑ 0)   ≡⟨ cong (just ∘ (_↑ 0))
                                                            (repeat*-↑-comm⁻ T m 0) ⟩
                just ((repeat m (_↑⁻ 0) T *⁻) ↑ 0)  ≡⟨ cong just $ *-↑-comm⁻ (repeat m (_↑⁻ 0) T) 0 ⟩
                just ((repeat m (_↑⁻ 0) T ↑⁻ 0) *⁻) ∎)
             (deterministic⇒minus n D)
    where open Eq (setoid (Maybe Ftyp))
  deterministic⇒minus n {Γ} (fdvar {m = m} () D) | nothing | _
  deterministic⇒minus n {Γ} (fdall D)     = aux n _ _ _ D
    where aux : ∀ {n} m {Γ} (S : Vec (Ftyp⁻ n) m) U T →
                  [ n ] Vec.foldl (λ _ → _) (flip _∷_) Γ S ⊢FD U <: T →
                  List.map _*⁻ Γ ⊢F Π⁺ m ∙ T <: Π⁻[ S ]∙ U
          aux .0 nil U T D                = fall (deterministic⇒minus _ D) fvrefl
          aux .(suc _) (x ‼ S) U T D      = fall ftop (aux _ S U T D)
