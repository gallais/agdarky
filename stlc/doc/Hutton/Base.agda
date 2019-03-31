module Hutton.Base where

open import Data.Unit
open import Data.List.Base
open import Generic.Syntax

-- Hutton's Razor: the smallest language needed to demonstrate a feature
-- Here we take: H = x | H + H

hutton : Desc ⊤

-- hutton is a description of a language where the notion of type is unit (⊤)
-- aka. there is no typing information

hutton = `X [] _ (`X [] _ (`∎ _))

-- it declares one constructor
-- (for the _+_ operator)

-- _+_ takes two subterms
-- (declared using the constructor `X)

-- both of which live in the same context
-- (the extension is the empty list [])

-- both of which don't have an interesting type
-- (_ is filled in by Agda: ⊤'s only value is tt)

-- And the return type of that constructor is not interesting
-- (again: this is an untyped language)

open import Data.Product
open import Relation.Binary.PropositionalEquality

pattern add' l r = (l , r  , refl)
pattern add l r  = `con (add' l r)

double : TM hutton _ → TM hutton _
double x = add x x

open import Data.Nat.Base
open import var
open import environment
open import Generic.Semantics

Value : ⊤ ─Scoped
Value _ _ = ℕ

sem : Sem hutton Value Value
Sem.th^𝓥 sem = λ v ρ → v
Sem.var   sem = λ n → n
Sem.alg   sem = λ where
  (add' l r) → l + r

eval : TM hutton _ → ℕ
eval = Sem.closed sem
