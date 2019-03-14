module Types where

open import Level
open import Data.String
open import Data.Nat using (ℕ)
open import Data.Maybe using (Maybe ; maybe′)
open import Data.Sum as Sum
open import Function

open import Category.Functor
open import Category.Applicative
open import Category.Monad
import Function.Identity.Categorical as Id

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

module Sumₗ {a} (A : Set a) (b : Level) where

  Sumₗ : Set (a ⊔ b) → Set (a ⊔ b)
  Sumₗ B = A ⊎ B

  functor : RawFunctor Sumₗ
  functor = record { _<$>_ = map id }

  applicative : RawApplicative Sumₗ
  applicative = record
    { pure = inj₂
    ; _⊛_ = [ const ∘ inj₁ , map id ]′
    }

  monadT : ∀ {M} → RawMonad M → RawMonad (M ∘′ Sumₗ)
  monadT M = record
    { return = M.pure ∘ inj₂
    ; _>>=_  = λ ma f → ma M.>>= [ M.pure ∘′ inj₁ , f ]′
    } where module M = RawMonad M

  monad : RawMonad Sumₗ
  monad = monadT Id.monad

module Result where

  open Sumₗ Error zero public
