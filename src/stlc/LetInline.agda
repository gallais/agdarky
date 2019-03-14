module LetInline where

open import Data.List.Base
open import Data.Product
open import environment
open import Language
open import Generic.Semantics
open import Generic.Semantics.Syntactic
open import Function

open Internal

LetInline : Sem internal Typed Typed
Sem.th^𝓥 LetInline = th^Tm
Sem.var   LetInline = id
Sem.alg   LetInline = λ where
  (_ , `let' e `in b) → extract b (ε ∙ e)
  p → Sem.alg Substitution p

let-inline : ∀ {σ} → Typed σ [] → Typed σ []
let-inline = Sem.closed LetInline
