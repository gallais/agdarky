module Main where

open import Data.Product
open import Data.String
open import Data.Sum.Base
open import Text.Parser.Position
open import Function

open import Language
open import Types
open import Parse
open import Scopecheck
open import Typecheck
open import LetInline
open import Print

open import Category.Monad
open RawMonad Result.monad

pipeline : String → Result String
pipeline str = do
  parsed         ← parse str
  (scoped , mp)  ← scopecheck parsed
  (σ , typed)    ← typecheck scoped
  let simplified = let-inline typed
  pure $ print simplified mp

open import Agda.Builtin.Equality

-- Success

_ : pipeline "(λa.a : `a → `a)" ≡ inj₂ "(λa.a : `a → `a)"
_ = refl

_ : pipeline "(λf.λx. let y = f x in y : (`a → `b) → (`a → `b))"
  ≡ inj₂ "(λa.λb.a b : (`a → `b) → `a → `b)"
_ = refl

_ : pipeline "(λf.λx. f (let y = x in y) x : (`a → `a → `b) → `a → `b)"
  ≡ inj₂ "(λa.λb.a b b : (`a → `a → `b) → `a → `b)"
_ = refl

_ : pipeline "(λg.λf.λa. let b = f a in g a b : (`a → `b → `c) → (`a → `b) → `a → `c)"
  ≡ inj₂ "(λa.λb.λc.a c (b c) : (`a → `b → `c) → (`a → `b) → `a → `c)"
_ = refl

-- Errors

_ : pipeline "(λa.a : A → A)" ≡ inj₁ (At 0 ∶ 8 ParseError )
_ = refl

_ : pipeline "(λa.b : `a → `a)" ≡ inj₁ (At 0 ∶ 3 OutOfScope "b")
_ = refl

_ : pipeline "(λa.a : `a → `b)" ≡ inj₁ (At 0 ∶ 3 Expected α 1 Got α 0)
_ = refl

_ : pipeline "(λa.λf.λx. f a x : `a → (`a → `b → `c) → `c)"
  ≡ inj₁ (At 0 ∶ 7 NotAnArrow α 2)
_ = refl
