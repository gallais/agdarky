module Hutton.Constant where

open import Data.Unit
open import Data.List.Base as List
open import Data.Nat.Base
open import Generic.Syntax

------------------------------------------------------------------------
-- SYNTAX: description in the universe of syntaxes with binding

-- Hutton's Razor reloaded
-- This time we take: H = x | n | H + H
-- where n is a natural number

data Tag : Set where
  Add Lit : Tag

hutton : Desc ⊤

-- it uses a Tag to distinguish two constructors:
-- the _+_ operator we have already seen
-- and a constructor for literals

hutton = `σ Tag λ where
  Add → `X [] _ (`X [] _ (`∎ _))
  Lit → `σ ℕ λ _ → `∎ _

-- `σ is used in one case to offer a choice of construtors and in another
-- to store a value in a constructor.

open import Data.Product
open import Relation.Binary.PropositionalEquality

-- We can once more introduce pattern synonyms to hide the fact that we
-- are using an encoding

pattern add' l r = (Add , l , r  , refl)
pattern add l r  = `con (add' l r)

double : TM hutton _ → TM hutton _
double x = add x x

pattern lit' n = (Lit , n , refl)
pattern lit n = `con (lit' n)

five : TM hutton _
five = lit 5

------------------------------------------------------------------------
-- SEMANTICS: scope-and-type preserving fold-like traversal

-- We can once more define our language's denotational semantics

open import Data.Nat.Base
open import var
open import environment
open import Generic.Semantics

Value : ⊤ ─Scoped
Value _ _ = ℕ

-- It is essentially the same except for the new lit' case we had to add.

Eval : Sem hutton Value Value
Sem.th^𝓥 Eval = λ v ρ → v
Sem.var   Eval = λ n → n
Sem.alg   Eval = λ where
  (add' l r) → l + r
  (lit' n)   → n

eval : TM hutton _ → ℕ
eval = Sem.closed Eval

-- 5 + 5 ≡ 10

_ : eval (double five) ≡ 10
_ = refl

------------------------------------------------------------------------

-- But we can also have more subtle semantics e.g. constant folding:
-- where values are now terms of the language itself.

open import Generic.Semantics.Syntactic

Fold : Sem hutton (Tm hutton _) (Tm hutton _)
Sem.th^𝓥 Fold = th^Tm    -- generic lemma: terms are always thinnable
Sem.var   Fold = λ t → t  -- values and result are the same type
Sem.alg   Fold = λ where
-- Here is the interesting part: we are simplifying the terms.
-- Note that the subterms l and r in the pattern (add' l r) have
-- already been simplified.
  (add' (lit 0) t)       → t
  (add' t (lit 0))       → t
  (add' (lit m) (lit n)) → lit (m + n)
  (add' t u)             → add t u
  (lit' n)               → lit n

fold : ∀ n → let Γ = List.replicate n _ in Tm hutton _ _ Γ → Tm hutton _ _ Γ
fold n = Sem.sem Fold (pack `var)

-- (0 + (x₂ + 0)) + (3 + 4) ≡ x₂ + 7

_ : fold 3 (add (add (lit 0) (add (`var (s (s z))) (lit 0)))
                (add (lit 3) (lit 4)))
  ≡ add (`var (s (s z))) (lit 7)
_ = refl

-- Or even more subtle ones where we collapse *all* constants and quotient
-- the tree modulo associativity

-- Values are then a constant together with a list of variables read from left
-- to right in the tree:

record Essence (_ : ⊤) (Γ : List ⊤) : Set where
  constructor _:+_
  field literal   : ℕ
        variables : List (Var _ Γ)

-- Variables are interpreted as themselves and the computation delivers the
-- 'essence' of a computation.

Simpl : Sem hutton Var Essence
Sem.th^𝓥 Simpl = th^Var                 -- Variables are always thinnable (≈ renaming)
Sem.var   Simpl = λ s → (0 :+ (s ∷ [])) -- Their essence is the singleton list
Sem.alg   Simpl = λ where
  -- The addition of two essences yields a new one by:
  -- taking the sum of both literals
  -- appending the lists of variables (while respecting the left to right ordering)
  (add' (m :+ xs) (n :+ ys)) → (m + n) :+ (xs ++ ys)
  -- The essence of a literal is its value together with the empty list of variables
  (lit' n)                   → n :+ []

open import Function

simplify : ∀ n → let Γ = List.replicate n _ in Tm hutton _ _ Γ → Tm hutton _ _ Γ
simplify Γ t = case Sem.sem Simpl (pack (λ v → v)) t of λ where
  -- we clean up after ourselves: if the literal is 0,
  -- we don't bother returning it
  (0 :+ (x ∷ xs)) → List.foldl cons (`var x) xs
  (n :+ xs)       → List.foldl cons (lit n) xs

    where cons = λ t v → add t (`var v)


-- (3 + (x₀ + x₁)) + (x₂ + (2 + 12)) ≡ 15 + x₀ + x₁ + x₂

_ : simplify 3 (add (add (lit 3) (add (`var z) (`var (s z))))
                    (add (`var (s (s z))) (add (lit 2) (lit 10))))
  ≡ add (add (add (lit 15) (`var z)) (`var (s z))) (`var (s (s z)))
_ = refl

-- ((x₀ + 0) + x₁) + (x₂ + (x₀ + x₀)) ≡ x₀ + x₁ + x₂ + x₀ + x₀

_ : simplify 3 (add (add (add (`var z) (lit 0)) (`var (s z)))
                    (add (`var (s (s z))) (add (`var z) (`var z))))
  ≡ add (add (add (add (`var z)
                       (`var (s z)))
                       (`var (s (s z))))
                       (`var z))
                       (`var z)
_ = refl



-- But all of this is really language specific...
