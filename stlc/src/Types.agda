module Types where

import Level as L
open import Category.Monad
open import Category.Monad.State
open import Data.String as String using (String; _++_)
import Data.String.Unsafe as String
open import Data.Product as Prod using (_×_; _,_; proj₁)
open import Data.List.Base using ([])
open import Data.Nat as ℕ using (ℕ)
open import Data.Maybe.Base using (Maybe; just; nothing; maybe′)
import Data.Maybe.Categorical as MC
open import Data.Sum.Base as Sum
import Data.Sum.Categorical.Left as Sumₗ
open import Function

open import Text.Parser.Position as Position using (Position)

open import Language hiding (show)

--------------------------------------------------------------------------------
-- Error type

data Error (A : Set) : Set where
  At_ParseError             : Position → Error A
  At_OutOfScope_            : Position → String → Error A
  At_Expected_Got_          : Position → Type A → Type A → Error A
  At_NotAnArrow_            : Position → Type A → Error A
  At_NotAProduct_           : Position → Type A → Error A
  At_ErrorWhenPrintingError : Position → Error A

show : Error String → String
show err = case err of λ where
  (At p ParseError)             → at p "parse error."
  (At p OutOfScope x)           → at p $ x ++ " is out of scope."
  (At p Expected σ Got τ)       → at p $ "expected type " ++ Language.show σ
                                      ++ " but got type " ++ Language.show τ ++ " instead."
  (At p NotAnArrow σ)           → at p $ "the type " ++ Language.show σ ++ " is not an arrow type."
  (At p NotAProduct σ)          → at p $ "the type " ++ Language.show σ ++ " is not a product type."
  (At p ErrorWhenPrintingError) → at p $ "error when printing error."

    where at : Position → String → String
          at p str = "At " ++ Position.show p ++ ": " ++ str

Result : Set → Set → Set
Result E = Sumₗ.Sumₗ (Error E) L.zero

module Result where

  monad : ∀ E → RawMonad (Result E)
  monad E = Sumₗ.monad (Error E) L.zero

  fail : ∀ {E A} → Error E → Result E A
  fail = inj₁

  fromMaybe : ∀ {E A} → Error E → Maybe A → Result E A
  fromMaybe = maybe′ inj₂ ∘′ fail

-- Data.AVL is not quite usable with String at the moment IIRC
-- So instead I'm using a quick and dirty representation
import Data.Map as M

private
  module RMap = M.Map ℕ._≟_ String
module Map  = M.Map String._≟_ ℕ
open Map using (Map; RMap) public

Compiler : Set → Set → Set
Compiler E = State (Map × ℕ) ∘′ (Error E ⊎_)

module Compiler where

  monad : ∀ E → RawMonad (Compiler E)
  monad E = Sumₗ.monadT (Error E) L.zero (StateMonad _)

  liftResult : ∀ {E A} → Error E ⊎ A → Compiler E A
  liftResult = _,_

  liftState : ∀ {E A} → State (Map × ℕ) A → Compiler E A
  liftState = let open RawMonad (StateMonad _) in inj₂ <$>_

  getMap : ∀ {E} → Compiler E Map
  getMap = liftState $ λ where s@(mp , n) → (mp , s)

  fail : ∀ {E A} → Error E → Compiler E A
  fail = liftResult ∘′ Result.fail

  fromMaybe : ∀ {E A} → Error E → Maybe A → Compiler E A
  fromMaybe e ma = liftResult $ Result.fromMaybe e ma

  run : ∀ {E A} → Compiler E A → Result E A
  run m = proj₁ (m ([] , 0))


module PrettyPrint where

  open RawMonad (MC.monad {L.zero}) using (_<$>_; _⊛_)

  ppType : RMap → Type ℕ → Maybe (Type String)
  ppType rm (α k)   = α <$> RMap.assoc k rm
  ppType rm (σ ⊗ τ) = _⊗_ <$> ppType rm σ ⊛ ppType rm τ
  ppType rm (σ ⇒ τ) = _⇒_ <$> ppType rm σ ⊛ ppType rm τ

  ppError : RMap → Error ℕ → Error String
  ppError rm err = case err of λ where
    (At p ParseError)             → At p ParseError
    (At p OutOfScope x)           → At p OutOfScope x
    (At p Expected σ Got τ)       →
      case At p Expected_Got_ <$> ppType rm σ ⊛ ppType rm τ of λ where
        nothing    → At p ErrorWhenPrintingError
        (just err) → err
    (At p NotAnArrow σ)           →
      case At p NotAnArrow_ <$> ppType rm σ of λ where
        nothing    → At p ErrorWhenPrintingError
        (just err) → err
    (At p NotAProduct σ)           →
      case At p NotAProduct_ <$> ppType rm σ of λ where
        nothing    → At p ErrorWhenPrintingError
        (just err) → err
    (At p ErrorWhenPrintingError) → At p ErrorWhenPrintingError


ppCompiler : ∀ {A} → Compiler ℕ A → Compiler String A
ppCompiler m = let open RawMonadState (StateMonadState _) in do
  v  ← m
  mp ← proj₁ <$> get
  pure $ Sum.map₁ (PrettyPrint.ppError (Map.invert mp)) v
