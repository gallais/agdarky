module Typecheck where

open import Data.Product
open import Data.Nat
open import Data.Sum as Sum
open import Data.String
open import Data.List hiding (lookup)
open import Data.List.All hiding (lookup)
open import Function

open import Category.Monad

open import var
open import environment
open import Generic.Syntax
open import Generic.Semantics

open import Text.Parser.Position

open import Language
open Surface
open Internal

Typing : List Mode → Set
Typing = All (const (Type ℕ))

support : ∀ Γ → Typing Γ → List (Mode × Type ℕ)
support []       []       = []
support (m ∷ ms) (σ ∷ σs) = (m , σ) ∷ support ms σs

Var- : Mode → List Mode → Set
Var- m Γ = ∀ γ → ∃ λ σ → Var σ (support Γ γ)

th^Var- : ∀ {m} → Thinnable (Var- m)
th^Var- v ρ δ = map₂ (unwind _ δ ρ) $ v (rewind _ δ ρ) where

  rewind : ∀ Γ {Δ} → Typing Δ → Thinning Γ Δ → Typing Γ
  rewind []      δ ρ = []
  rewind (σ ∷ Γ) δ ρ = get (lookup ρ z) δ ∷ rewind Γ δ (select extend ρ)

  got : ∀ {Δ m} (k : Var m Δ) (γ : Typing Δ) → Var (m , get k γ) (support Δ γ)
  got z     (σ ∷ _) = z
  got (s k) (_ ∷ γ) = s (got k γ)

  unwind : ∀ Γ {Δ σ} δ ρ → Var σ (support Γ (rewind Γ δ ρ)) → Var σ (support Δ δ)
  unwind []      δ ρ ()
  unwind (σ ∷ Γ) δ ρ z     = got (lookup ρ z) δ
  unwind (σ ∷ Γ) δ ρ (s v) = unwind Γ δ (select extend ρ) v

data Error : Set where
  Expected_Got_ : Type ℕ → Type ℕ → Error

Result : Set → Set
Result = (Position × Error) ⊎_

monad : RawMonad Result
monad = record { return = inj₂ ; _>>=_ = flip [ inj₁ ,_]′ }

Type- : Mode → List Mode → Set
Type- Infer Γ = ∀ γ   → Result (∃ λ σ → Typed (Infer , σ) (support Γ γ))
Type- Check Γ = ∀ γ σ → Result (Typed (Check , σ) (support Γ γ))

open RawMonad monad hiding (return)

Typecheck : Sem (surface ℕ) Var- Type-
Sem.th^𝓥 Typecheck {m} = th^Var- {m}
Sem.var   Typecheck {m} = case m return (λ m → Var- m _ → Type- m _) of λ where
  Infer v γ → {!!}
  Check → {!!}
Sem.alg   Typecheck = {!!}

typecheck : Scoped Infer [] → Result (∃ λ σ → Typed (Infer , σ) [])
typecheck t = Sem.closed Typecheck t []
