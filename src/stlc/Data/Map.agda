module Data.Map where

open import Data.Bool
open import Data.Product
open import Data.List as List
open import Data.Maybe
open import Function

open import Relation.Nullary
open import Relation.Nullary.Decidable
open import Relation.Binary
open import Relation.Binary.PropositionalEquality

module Map {A : Set} (eq? : Decidable {A = A} _≡_) (B : Set)  where

  Map : Set
  Map = List (A × B)

  empty : Map
  empty = []

  set : A → B → Map → Map
  set a b mp = (a , b) ∷ mp

  assoc : A → Map → Maybe B
  assoc a = flip foldr nothing $ uncurry $ λ a′ b ih →
    if ⌊ eq? a a′ ⌋ then just b else nothing
