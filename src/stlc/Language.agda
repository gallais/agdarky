module Language where

open import Size
open import Data.Unit
open import Data.Product hiding (,_)
open import Data.Nat
open import Data.Fin
open import Data.List as List
open import Data.List.All
open import Data.List.Membership.Propositional
open import Data.String as String
open import Function
open import Relation.Nullary
open import Relation.Binary using (Decidable)
open import Relation.Binary.PropositionalEquality

open import var using (z ; s)
open import Generic.Syntax
open import Generic.AltSyntax
open import Text.Parser.Position

infixr 6 _⇒_
data Type (A : Set) : Set where
  α   : A → Type A
  _⇒_ : (σ τ : Type A) → Type A

data Mode : Set where
  Infer Check : Mode

eqdecMode : Decidable {A = Mode} _≡_
eqdecMode Infer Infer = yes refl
eqdecMode Infer Check = no (λ ())
eqdecMode Check Infer = no (λ ())
eqdecMode Check Check = yes refl

data `Bidi : Set where
  Cut App Lam Emb : `Bidi

-- Throwing in some useful combinators

module _ {I : Set} where

  `κ_`×_ : Set → Desc I → Desc I
  `κ A `× d = `σ A $ const d

  Located : Desc I → Desc I
  Located d = `κ Position `× d

module Surface where

-- I'm adding useless `κ_`×_ parts to keep the layout the
-- same between surface and internal. This will allow us to
-- use the same pattern synonyms for both!
  surface : Set → Desc Mode
  surface A = Located $ `σ `Bidi $ λ where
    Cut → `κ Type A `× `X [] Check (`∎ Infer)
    App → `κ ⊤      `× `X [] Infer (`X [] Check (`∎ Infer))
    Lam → `κ ⊤      `× `X (Infer ∷ []) Check (`∎ Check)
    Emb → `κ ⊤      `× `X [] Infer (`∎ Check)

  Parsed : {i : Size} → Mode → Set
  Parsed {i} = Raw (surface String) i

  Scoped : {i : Size} → Mode → List Mode → Set
  Scoped {i} = Tm (surface ℕ) i


module Internal where

  internal : Desc (Mode × Type ℕ)
  internal = Located $ `σ `Bidi $ λ where
    Cut → `σ (Type ℕ)          $ λ σ →
          `X [] (Check , σ) (`∎ (Infer , σ))
    App → `σ (Type ℕ × Type ℕ) $ uncurry $ λ σ τ →
          `X [] (Infer , σ ⇒ τ) (`X [] (Check , σ) (`∎ (Infer , τ)))
    Lam → `σ (Type ℕ × Type ℕ) $ uncurry $ λ σ τ →
          `X ((Infer , σ) ∷ []) (Check , τ) (`∎ (Check , σ ⇒ τ))
    Emb → `σ (Type ℕ)          $ λ σ →
          `X [] (Infer , σ) (`∎ (Check , σ))

  Typed : {i : Size} → (Mode × Type ℕ) → List (Mode × Type ℕ) → Set
  Typed {i} = Tm internal i


-- Traditional pattern synonyms (usable on the LHS only)
pattern _`∶'_ t σ = (Cut , σ , t , refl)
pattern _`∶_  t σ = `con (_ , t `∶' σ)
pattern _`$'_ f t = (App , _ , f , t , refl)
pattern _`$_  f t = `con (_ , f `$' t)
pattern `λ'_  b   = (Lam , _ , b , refl)
pattern `λ_   b   = `con (_ , `λ' b)
pattern `-'   t   = (Emb , _ , t , refl)
pattern `-    t   = `con (_ , `-' t)

-- Position-aware pattern synonyms (usable both on the LHS and RHS)
pattern _>_`∶'_ r t σ = (r , Cut , σ , t , refl)
pattern _>_`∶_  r t σ = `con (r > t `∶' σ)
pattern _>_`$'_ r f t = (r , App , _ , f , t , refl)
pattern _>_`$_  r f t = `con (r > f `$' t)
pattern _>`λ'_  r b   = (r , Lam , _ , b , refl)
pattern _>`λ_   r b   = `con (r >`λ' b)
pattern _>`-'_  r t   = (r , Emb , _ , t , refl)
pattern _>`-_   r t   = `con (r >`-' t)


-- Examples of terms of differnent languages using the same pattern synonyms
-- Here we use `start' as a placeholder for positions

_ : Surface.Scoped Check []
_ = start >`λ (start >`- `var z)

_ : ∀ {σ} → Internal.Typed (Check , σ ⇒ σ) []
_ = start >`λ (start >`- `var z)
