module Data.List.Relation.Unary.All.Extras where

open import Data.List.Base as List
open import Data.List.All as Listₚ
open import Data.Product
open import Function
open import Relation.Unary

module _ {a p} {A : Set a} {P : Pred A p} where

  fromList : (xs : List (∃ P)) → All P (List.map proj₁ xs)
  fromList []              = []
  fromList ((x , p) ∷ xps) = p ∷ fromList xps

  toList : ∀ {xs} → All P xs → List (∃ P)
  toList []         = []
  toList (px ∷ pxs) = (-, px) ∷ toList pxs

self : ∀ {a} {A : Set a} {xs : List A} → All (const A) xs
self = Listₚ.tabulate (λ {x} _ → x)
