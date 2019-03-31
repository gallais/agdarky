module Hutton.Constant where

open import Data.Unit
open import Data.List.Base as List
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

Eval : Sem hutton Value Value
Sem.th^𝓥 Eval = λ v ρ → v
Sem.var   Eval = λ n → n
Sem.alg   Eval = λ where
  (add' l r) → l + r
  (lit' n)   → n

eval : TM hutton _ → ℕ
eval = Sem.closed Eval

-- 5 + 5 ≡ 10

_ : eval (add five five) ≡ 10
_ = refl

open import Generic.Semantics.Syntactic

Fold : Sem hutton (Tm hutton _) (Tm hutton _)
Sem.th^𝓥 Fold = th^Tm
Sem.var   Fold = λ t → t
Sem.alg   Fold = λ where
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

record Essence (_ : ⊤) (Γ : List ⊤) : Set where
  constructor _:+_
  field literal   : ℕ
        variables : List (Var _ Γ)

Simpl : Sem hutton Essence Essence
Sem.th^𝓥 Simpl = λ where (n :+ xs) ρ → n :+ List.map (λ v → th^Var v ρ) xs
Sem.var   Simpl = λ s → s
Sem.alg   Simpl = λ where
  (add' (m :+ xs) (n :+ ys)) → (m + n) :+ (xs ++ ys)
  (lit' n)                   → n :+ []

simplify : ∀ n → let Γ = List.replicate n _ in Tm hutton _ _ Γ → Tm hutton _ _ Γ
simplify Γ t = let (n :+ xs) = Sem.sem Simpl (pack (λ v → 0 :+ (v ∷ []))) t in
               List.foldl (λ t v → add t (`var v)) (lit n) xs


-- (3 + (x₀ + x₁)) + (x₂ + (2 + 12)) ≡ 15 + x₀ + x₁ + x₂

_ : simplify 3 (add (add (lit 3) (add (`var z) (`var (s z))))
                    (add (`var (s (s z))) (add (lit 2) (lit 10))))
  ≡ add (add (add (lit 15) (`var z)) (`var (s z))) (`var (s (s z)))
_ = refl
