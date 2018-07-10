module Types where

open import Data.String
open import Data.Nat
open import Data.Maybe hiding (monad)
open import Data.Sum as Sum
open import Function

open import Category.Monad
open import Category.Monad.State

open import Text.Parser.Position

open import Language

--------------------------------------------------------------------------------
-- Error type

data Error : Set where
  At_ParseError    : Position → Error
  At_OutOfScope_   : Position → String → Error
  At_Expected_Got_ : Position → Type ℕ → Type ℕ → Error
  At_NotAnArrow_   : Position → Type ℕ → Error

data Result (A : Set) : Set where
  hardFail : Error → Result A
  softFail : Error → Result A
  value    : A → Result A

fail : ∀ {A} → Error → Result A
fail = softFail

fromMaybe : ∀ {A} → Error → Maybe A → Result A
fromMaybe = maybe′ value ∘′ softFail

fromSum : ∀ {A B : Set} → (A → Error) → A ⊎ B → Result B
fromSum f = [ fail ∘′ f , value ]′

monad : RawMonad Result
monad = record
  { return = value
  ; _>>=_  = λ ra f → case ra of λ where
    (hardFail e) → hardFail e
    (softFail e) → softFail e
    (value v)    → f v
  }

--------------------------------------------------------------------------------
-- Monad stack used for parsing

ParserM = StateT Position Result

instance

  monad-M : RawMonad ParserM
  monad-M = StateTMonad Position monad

  monad0-M : RawMonadZero ParserM
  monad0-M = record
    { monad = monad-M
    ; ∅     = fail ∘′ At_ParseError
    }

  monad+-M : RawMonadPlus ParserM
  monad+-M = record
    { monadZero = monad0-M
    ; _∣_       = λ ma₁ ma₂ s → case ma₁ s of λ where
      (softFail _) → ma₂ s
      r            → r
    }

commit : ∀ {A} → ParserM A → ParserM A
commit ma s = case ma s of λ where
  (softFail e) → hardFail e
  r            → r
