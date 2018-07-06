module Parse where

import Level
open import Data.Nat
open import Data.Empty
open import Data.Product
open import Data.Char
open import Data.String as String
open import Data.Sum
open import Data.Sum.Categorical
open import Data.List hiding ([_])
open import Data.List.NonEmpty as NE hiding ([_])
open import Data.List.Sized
open import Data.Maybe
open import Data.Vec hiding ([_] ; _>>=_)
open import Function

open import Category.Monad
open import Category.Monad.State

open import Induction.Nat.Strong

open import Data.Subset
open import Relation.Binary.PropositionalEquality.Decidable
open import Relation.Unary.Indexed
open import Text.Parser.Types
open import Text.Parser.Instruments
open import Text.Parser.Position
open import Text.Parser.Combinators
open import Text.Parser.Char

open import Language
open Surface

private M = StateT Position (Position ⊎_)

P : Parameters
Parameters.Tok  P = Char
Parameters.Toks P = Vec Char
Parameters.Pos  P = Position
Parameters.Ann  P = ⊥
Parameters.M    P = StateT Position (Position ⊎_)

instance

  instrP : Instrumented P
  withAnnotation instrP = λ _ ma → ma
  recordToken    instrP = λ c p → inj₂ (_ , next c p)
  getPosition    instrP = λ p → inj₂ (p , p)
  getAnnotation  instrP = λ p → inj₂ (nothing , p)

  monad-M : RawMonad M
  monad-M = record
    { return = λ a p → inj₂ (a , p)
    ; _>>=_  = λ ma f p → [ inj₁ , uncurry f ]′ (ma p)
    }

  monad+-M : RawMonadPlus M
  monad+-M = record
    { monadZero = record { monad = monad-M ; ∅ = inj₁ }
    ; _∣_       = λ ma₁ ma₂ p → [ const (ma₂ p) , inj₂ ]′ (ma₁ p)
    }

type : [ Parser P (Type String) ]
type = fix _ $ λ rec →
  let name = String.fromList⁺ <$> (char '`' &> box alphas⁺) in
  chainr1 (α <$> name <|> parens rec)
          (box $ _⇒_ <$ withSpaces (char '→'))

record Bidirectional (n : ℕ) : Set where
  field infer : Parser P (Parsed Infer) n
        check : Parser P (Parsed Check) n
open Bidirectional

open RawMonad (StateTMonad Position (monadₗ Position Level.zero))

bidirectional : [ Bidirectional ]
bidirectional = fix Bidirectional $ λ rec →
  {!!}

parse : ∀ m → [ Parser P (Parsed m) ]
parse Infer = infer bidirectional
parse Check = check bidirectional
