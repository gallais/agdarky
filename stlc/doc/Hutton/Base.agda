module Hutton.Base where

open import Data.Unit
open import Data.List.Base as List
open import Generic.Syntax

------------------------------------------------------------------------
-- SYNTAX: description in the universe of syntaxes with binding

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

-- We can use pattern synonyms to hide the fact we are using a universe of
-- syntaxes with binding

pattern add' l r = (l , r  , refl)
pattern add l r  = `con (add' l r)

-- They can be used on the RHS

double : TM hutton _ → TM hutton _
double x = add x x

-- But also on the LHS:

right : ∀ {Γ} → Tm hutton _ _ Γ → Tm hutton _ _ Γ
right (add l r) = r
right (`var x)  = `var x

-- We discover here the notion of variables: syntaxes with binding are
-- automatically endowed with variables.

------------------------------------------------------------------------
-- SEMANTICS: scope-and-type preserving fold-like traversal

open import Data.Nat.Base
open import var
open import environment
open import Generic.Semantics

-- The notion of values for a Semantics are always scoped. This way we
-- can write type-and-scope preserving traversals

Value : ⊤ ─Scoped
Value _ _ = ℕ

Eval : Sem    -- a semantics
       hutton -- for terms in hutton's razor
       Value  -- where variables are assigned a Value
       Value  -- and the overall computation returns a Value

-- In general for a traversal on a syntax with binding to be scope preversing,
-- we need to be able to embed the scoped values assigned to variables into
-- larger contexts. This allows us to go under binder.
-- Here Value is scope independent. As such it is trivially thinnable (i.e.
-- stable under scope extensions).
Sem.th^𝓥 Eval = λ v ρ → v

-- When we look up the value associated to a variable, we need to return
-- something which has the type of the overall computation. Here they match
-- up so we can use the identity function
Sem.var   Eval = λ n → n

-- Finally we have to define an algebra which interprets every constructor
-- provided that the subterms already have been interpreted. Here we transform
-- the syntactic construct add into the addition on natural numbers
Sem.alg   Eval = λ where
  (add' l r) → l + r

-- We can evaluate terms by giving an interpretation to each of their variables
eval : ∀ (n : ℕ) → let Γ = List.replicate n _ in (Γ ─Env) Value [] → Tm hutton _ _ Γ → ℕ
eval n ρ t = Sem.sem Eval ρ t

open import Relation.Binary.PropositionalEquality

-- x₀ + x₁ ≡ 12 under the assumption that x₀ = 4 and x₁ = 8

_ : eval 2 (ε ∙ 4 ∙ 8) (add (`var z) (`var (s z)))
  ≡ 12
_ = refl
