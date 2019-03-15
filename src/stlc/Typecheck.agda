module Typecheck where

open import Data.Product as Product
open import Data.Nat as ℕ using (ℕ; _≟_)
open import Data.List hiding (lookup ; fromMaybe)
open import Data.List.Relation.Unary.All as All hiding (lookup)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.List.Membership.Propositional
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Data.Maybe hiding (fromMaybe)
open import Function

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

fromTyping : ∀ ms → Typing ms → List (Mode × Type ℕ)
fromTyping []       []       = []
fromTyping (m ∷ ms) (σ ∷ σs) = (m , σ) ∷ fromTyping ms σs

Elab : (Mode × Type ℕ) ─Scoped → Mode × Type ℕ → (ms : List Mode) → Typing ms → Set
Elab T σ ms Γ = T σ (fromTyping ms Γ)

data Var- : Mode ─Scoped where
  `var : ∀ {ms} → (infer : ∀ Γ → Σ[ σ ∈ Type ℕ ] Elab Var (Infer , σ) ms Γ) →
         Var- Infer ms

var0 : ∀ {ms} → Var- Infer (Infer ∷ ms)
var0 = `var (λ where (σ ∷ _) → σ , z)

toVar : ∀ {m : Mode} {ms} → m ∈ ms → Var m ms
toVar (here refl) = z
toVar (there v) = s (toVar v)

fromVar : ∀ {m : Mode} {ms} → Var m ms → m ∈ ms
fromVar z = here refl
fromVar (s v) = there (fromVar v)

coth^Typing : ∀ {ms ns} → Typing ns → Thinning ms ns → Typing ms
coth^Typing Δ ρ = All.tabulate (λ x∈Γ → All.lookup Δ (fromVar (lookup ρ (toVar x∈Γ))))

lookup-fromVar : ∀ {m ms} Δ (v : Var m ms) →
                 Var (m , All.lookup Δ (fromVar v)) (fromTyping ms Δ)
lookup-fromVar (_ ∷ _) z     = z
lookup-fromVar (_ ∷ _) (s v) = s (lookup-fromVar _ v)

erase^coth : ∀ ms {m σ ns} Δ (ρ : Thinning ms ns) →
             Var (m , σ) (fromTyping ms (coth^Typing Δ ρ)) → Var (m , σ) (fromTyping ns Δ)
erase^coth []       Δ ρ ()
erase^coth (m ∷ ms) Δ ρ z     = lookup-fromVar Δ (lookup ρ z)
erase^coth (m ∷ ms) Δ ρ (s v) = erase^coth ms Δ (select extend ρ) v

th^Var- : ∀ {m} → Thinnable (Var- m)
th^Var- (`var infer) ρ = `var λ Δ →
  let (σ , v) = infer (coth^Typing Δ ρ) in
  σ , erase^coth _ Δ ρ v

isArrow : (σ⇒τ : Type ℕ) → Maybe (Σ[ στ ∈ Type ℕ × Type ℕ ] σ⇒τ ≡ uncurry _⇒_ στ)
isArrow (α _) = nothing
isArrow (σ ⇒ τ) = just ( _ , refl)

Type- : Mode → List Mode → Set
Type- Infer Γ = ∀ γ   → Result (∃ λ σ → Typed (Infer , σ) (fromTyping Γ γ))
Type- Check Γ = ∀ γ σ → Result (Typed (Check , σ) (fromTyping Γ γ))

open RawMonad Result.monad hiding (return)

Typecheck : Sem (surface ℕ) Var- Type-
Sem.th^𝓥 Typecheck = th^Var-
Sem.var   Typecheck = λ where (`var infer) γ → pure (map₂ `var (infer γ))
Sem.alg   Typecheck = λ where
  (r > t `∶' σ) γ     → (-,_ ∘ (r >_`∶ σ)) <$> t γ σ
  (r > f `$' t) γ     → do
    (σ⇒τ , f′)       ← f γ
    ((σ , τ) , refl) ← fromMaybe (At r NotAnArrow σ⇒τ) (isArrow σ⇒τ)
    t′               ← t γ σ
    pure $ -, r > f′ `$ t′
  (r >`λ' b) γ σ⇒τ → do
    ((σ , τ) , refl) ← fromMaybe (At r NotAnArrow σ⇒τ) (isArrow σ⇒τ)
    b′               ← b extend (ε ∙ var0) (σ ∷ γ) τ
    pure $ r >`λ b′
  (r >`let' e `in b) γ τ → do
    (σ , e′) ← e γ
    b′       ← b extend (ε ∙ var0) (σ ∷ γ) τ
    pure $ r >`let e′ `in b′
  (r >`-' t) γ σ   → do
    (τ , t′) ← t γ
    refl     ← fromMaybe (At r Expected σ Got τ) (decToMaybe $ eqdecType ℕ._≟_ τ σ)
    pure $ r >`- t′

Type-_ed : Mode → Set
Type- Infer ed = Result (∃ λ σ → Typed (Infer , σ) [])
Type- Check ed = ∀ σ → Result (Typed (Check , σ) [])

typecheck : ∀ {m} → Scoped m [] → Type- m ed
typecheck {Infer} t = Sem.closed Typecheck t []
typecheck {Check} t = Sem.closed Typecheck t []
