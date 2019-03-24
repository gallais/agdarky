module Eval where

open import Data.Nat.Base using (ℕ)
open import Data.List.Base
open import Data.Product as Prod
open import Function
open import Relation.Unary renaming (_⇒_ to _⟶_)
open import var
open import environment
open import Generic.Syntax
open import Generic.Semantics
open import Generic.Semantics.Syntactic
open import Language; open Internal
open import Text.Parser.Position

Model' : Type ℕ → List (Mode × Type ℕ) → Set
Model' (α k)   Γ = Position × Typed (Infer , α k) Γ
Model' (σ ⊗ τ) Γ = Position × Model' σ Γ × Model' τ Γ
Model' (σ ⇒ τ) Γ = Position × □ (Model' σ ⟶ Model' τ) Γ

Model : (Mode × Type ℕ) ─Scoped
Model (m , σ) = Model' σ

th^Model' : ∀ {σ} → Thinnable (Model' σ)
th^Model' {α k}   (r , t)     ρ = r , th^Tm t ρ
th^Model' {σ ⇒ τ} (r , f)     ρ = r , th^□ f ρ
th^Model' {σ ⊗ τ} (r , a , b) ρ = r , th^Model' a ρ , th^Model' b ρ

eval : Sem typed Model Model
Sem.th^𝓥 eval = th^Model'
Sem.var  eval = id
Sem.alg  eval = λ where
  (r , `λ' b)         → r , λ inc v → b inc (ε ∙ v)
  (r , f `$' t)       → extract (proj₂ f) t
  (r , `fst' t)       → proj₁ $ proj₂ t
  (r , `snd' t)       → proj₂ $ proj₂ t
  (r , a `,' b)       → (r , a , b)
  (r , t `∶' σ)       → t
  (r , `-' t)         → t
  (r , `let' e `in t) → extract t (ε ∙ e)

reify   : ∀ σ → ∀[ Model' σ ⟶ Typed (Check , σ) ]
reflect : ∀ σ → ∀[ const Position ⟶ Typed (Infer , σ) ⟶ Model' σ ]

reify (α k)   (r , t)     = r >`- t
reify (σ ⇒ τ) (r , t)     = r >`λ reify τ (t extend (reflect σ r (`var z)))
reify (σ ⊗ τ) (r , a , b) = r > reify σ a `, reify τ b

reflect (α k)   r t = r , t
reflect (σ ⊗ τ) r t = r , reflect σ r (r >`fst t) , reflect τ r (r >`snd t)
reflect (σ ⇒ τ) r t = r , λ inc v → reflect τ r (r > th^Tm t inc `$ reify σ v)
