module Main where

open import Data.Product
open import Data.String
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
