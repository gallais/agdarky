module Main where

import Level
open import Data.Nat.Properties
open import Data.Product as Product
open import Data.String
open import Data.Sum as Sum
open import Data.List as List
open import Function

open import Language
open import Types
open import Parse
open import Scopecheck
open import Typecheck
open import Print

open import Data.Map
open import Category.Monad
open import Text.Parser.Types
open import Text.Parser.Position

open RawMonad monad

pipeline : String → Result String
pipeline str = do
  parsed        ← parse str
  (scoped , mp) ← scopecheck parsed
  (σ , typed)   ← typecheck Infer scoped
  pure $ print typed mp
