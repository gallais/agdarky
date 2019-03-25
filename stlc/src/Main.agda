module Main where

open import Data.List.Base using ([]; _∷_)
open import Data.Sum.Base
open import Data.Product
open import Data.String.Base
open import Function

open import System.Environment
open import IO
open import Codata.Musical.Notation

import Types
open import Pipeline
open import Print

main = run $
  ♯ getArgs >>= λ where
    []       → ♯ (return _)
    (fp ∷ _) → ♯ (♯ readFiniteFile fp >>= λ str →
                  ♯ putStrLn ([ Types.show , unlines3 ]′ (pipeline str)))

  where unlines3 = λ where (a , b , c) → a ++ "\n" ++ b ++ "\n" ++ c
