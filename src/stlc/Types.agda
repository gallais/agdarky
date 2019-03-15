module Types where

open import Level
open import Data.String.Base
open import Data.Nat.Base using (ℕ)
open import Data.Maybe.Base using (Maybe ; maybe′)
open import Data.Sum.Base as Sum
open import Function

open import Text.Parser.Position

open import Language

--------------------------------------------------------------------------------
-- Error type

data Error : Set where
  At_ParseError    : Position → Error
  At_OutOfScope_   : Position → String → Error
  At_Expected_Got_ : Position → Type ℕ → Type ℕ → Error
  At_NotAnArrow_   : Position → Type ℕ → Error

Result : Set → Set
Result = Error ⊎_

fail : ∀ {A} → Error → Result A
fail = inj₁

fromMaybe : ∀ {A} → Error → Maybe A → Result A
fromMaybe = maybe′ inj₂ ∘′ fail

module Result where

  open import Data.Sum.Categorical.Left Error zero public
