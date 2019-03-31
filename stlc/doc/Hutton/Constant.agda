module Hutton.Constant where

open import Data.Unit
open import Data.List.Base
open import Data.Nat.Base
open import Generic.Syntax

-- Hutton's Razor reloaded
-- This time we take: H = x | n | H + H
-- where n is a natural number

data Tag : Set where
  Add Lit : Tag

hutton : Desc ⊤

-- it declares two constructors
-- (the _+_ operator we have already seen and a literal)

hutton = `σ Tag λ where
  Add → `X [] _ (`X [] _ (`∎ _))
  Lit → `σ ℕ λ _ → `∎ _

-- comment on `σ (used twice but with different meanings)

open import Data.Product
open import Relation.Binary.PropositionalEquality

pattern add' l r = (Add , l , r  , refl)
pattern add l r  = `con (add' l r)

double : TM hutton _ → TM hutton _
double x = add x x

pattern lit' n = (Lit , n , refl)
pattern lit n = `con (lit' n)

five : TM hutton _
five = lit 5



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
  (lit' n)   → n

eval : TM hutton _ → ℕ
eval = Sem.closed sem

_ : eval (add five five) ≡ 10
_ = refl
