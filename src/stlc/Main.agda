module Main where

open import Data.Product
open import Data.String
open import Data.Sum.Base using (inj₂)
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

_ : pipeline "(λa.a : `a → `a)" ≡ inj₂ "(λa.a : `a → `a)"
_ = refl

_ : pipeline "(λf.λx. let y = f x in y : (`a → `b) → (`a → `b))"
  ≡ inj₂ "(λa.λb.a b : (`a → `b) → `a → `b)"
_ = refl

_ : pipeline "(λf.λx. f (let y = x in y) x : (`a → `a → `b) → `a → `b)"
  ≡ inj₂ "(λa.λb.a b b : (`a → `a → `b) → `a → `b)"
_ = refl
