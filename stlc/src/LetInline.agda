module LetInline where

open import Data.List.Base
open import Data.Product
open import environment
open import Language
open import Generic.Semantics
open import Generic.Semantics.Syntactic
open import Function

open Internal

LetInline : Sem typed LetFree LetFree
Sem.th^𝓥 LetInline = th^Tm
Sem.var   LetInline = id
Sem.alg   LetInline = λ t → case letView t of λ where
  (Let r e b) → extract b (ε ∙ e)
  (¬Let p)    → Sem.alg Substitution p

let-inline : ∀ {σ} → Typed σ [] → LetFree σ []
let-inline = Sem.closed LetInline
