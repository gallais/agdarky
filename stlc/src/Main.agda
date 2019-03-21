module Main where

open import Data.List.Base
open import Data.Sum.Base
open import Function

open import System.Environment
open import IO
open import Codata.Musical.Notation

import Types
open import Pipeline

main = run $
  ♯ getArgs >>= λ where
    []       → ♯ (return _)
    (fp ∷ _) → ♯ (♯ readFiniteFile fp >>= λ str →
                  ♯ putStrLn ([ Types.show , const "success" ]′ (pipeline str)))
