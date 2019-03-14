module Typecheck where

open import Data.Product as Product
open import Data.Nat as ℕ hiding (_>_)
open import Data.List hiding (lookup ; fromMaybe)
open import Data.List.Relation.Unary.All hiding (lookup)
open import Data.Maybe hiding (fromMaybe)
open import Function
open import Relation.Binary.PropositionalEquality

open import Category.Monad

open import var hiding (_<$>_)
open import environment hiding (_<$>_)
open import Generic.Syntax
open import Generic.Semantics

open import Text.Parser.Position

open import Language
open Surface
open Internal
open import Types

Typing : List Mode → Set
Typing = All (const (Type ℕ))

support : ∀ Γ → Typing Γ → List (Mode × Type ℕ)
support []       []       = []
support (m ∷ ms) (σ ∷ σs) = (m , σ) ∷ support ms σs

Var- : Mode → List Mode → Set
Var- m Γ = ∀ γ → m ≡ Infer × ∃ λ σ → Var (m , σ) (support Γ γ)

var0 : ∀ {Γ} → Var- Infer (Infer ∷ Γ)
var0 (σ ∷ _) = refl , σ , z

th^Var- : ∀ {m} → Thinnable (Var- m)
th^Var- v ρ δ = map₂ (map₂ $ unwind _ δ ρ) $ v (rewind _ δ ρ) where

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


isArrow : (σ⇒τ : Type ℕ) → Maybe (Σ[ στ ∈ Type ℕ × Type ℕ ] σ⇒τ ≡ uncurry _⇒_ στ)
isArrow (α _) = nothing
isArrow (σ ⇒ τ) = just ( _ , refl)

Type- : Mode → List Mode → Set
Type- Infer Γ = ∀ γ   → Result (∃ λ σ → Typed (Infer , σ) (support Γ γ))
Type- Check Γ = ∀ γ σ → Result (Typed (Check , σ) (support Γ γ))

open RawMonad Result.monad hiding (return)

Typecheck : Sem (surface ℕ) Var- Type-
Sem.th^𝓥 Typecheck {m} = th^Var- {m}
Sem.var   Typecheck {m} = case m return (λ m → Var- m _ → Type- m _) of λ where
  Infer v γ → pure (Product.map₂ `var (proj₂ $ v γ))
  Check v γ → case (proj₁ $ v γ) of λ ()
Sem.alg   Typecheck = λ where
  (r > t `∶' σ) γ     → (-,_ ∘ (r >_`∶ σ)) <$> t γ σ
  (r > f `$' t) γ     → do
    (σ⇒τ , f′)       ← f γ
    ((σ , τ) , refl) ← fromMaybe (At r NotAnArrow σ⇒τ) (isArrow σ⇒τ)
    t′               ← t γ σ
    pure $ -, r > f′ `$ t′
  (r >`λ' b)    γ σ⇒τ → do
    ((σ , τ) , refl) ← fromMaybe (At r NotAnArrow σ⇒τ) (isArrow σ⇒τ)
    b′               ← b extend (ε ∙ var0) (σ ∷ γ) τ
    pure $ r >`λ b′
  (r >`-' t)    γ σ   → do
    (τ , t′) ← t γ
    refl     ← fromMaybe (At r Expected σ Got τ) (decToMaybe $ eqdecType ℕ._≟_ τ σ)
    pure $ r >`- t′

Type-_ed : Mode → Set
Type- Infer ed = Result (∃ λ σ → Typed (Infer , σ) [])
Type- Check ed = ∀ σ → Result (Typed (Check , σ) [])

typecheck : ∀ {m} → Scoped m [] → Type- m ed
typecheck {Infer} t = Sem.closed Typecheck t []
typecheck {Check} t = Sem.closed Typecheck t []
