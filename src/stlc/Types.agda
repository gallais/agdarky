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

Result : Set → Set
Result = Error ⊎_

fail : ∀ {A} → Error → Result A
fail = inj₁

fromMaybe : ∀ {A} → Error → Maybe A → Result A
fromMaybe = maybe′ inj₂ ∘′ fail

fromSum : ∀ {A B : Set} → (A → Error) → A ⊎ B → Result B
fromSum f = [ fail ∘′ f , inj₂ ]′

monad : RawMonad Result
monad = record
  { return = inj₂
  ; _>>=_  = [ const ∘ fail , _|>′_ ]
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
    ; _∣_       = λ ma₁ ma₂ p → [ const (ma₂ p) , inj₂ ]′ (ma₁ p)
    }
