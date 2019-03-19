module Language where

open import Data.Unit
open import Data.Empty
open import Data.Product
open import Data.Nat
open import Data.List as List
open import Data.List.Relation.Unary.All -- important for the pattern synonyms!
open import Data.String as String
open import Function
open import Function.Equivalence
open import Relation.Nullary
open import Relation.Nullary.Decidable as RNDec
open import Relation.Nullary.Product
open import Relation.Binary using (Decidable)
open import Relation.Binary.PropositionalEquality

open import var using (z; s; _─Scoped)
open import Generic.Syntax
open import Generic.AltSyntax
open import Text.Parser.Position

infixr 6 _⇒_
data Type (A : Set) : Set where
  α   : A → Type A
  _⇒_ : (σ τ : Type A) → Type A

data Mode : Set where
  Infer Check : Mode

eqdecMode : Decidable {A = Mode} _≡_
eqdecMode Infer Infer = yes refl
eqdecMode Infer Check = no (λ ())
eqdecMode Check Infer = no (λ ())
eqdecMode Check Check = yes refl

module _ {A : Set} where

 α-equivalence : {a₁ a₂ : A} → (a₁ ≡ a₂) ⇔ (α a₁ ≡ α a₂)
 α-equivalence = equivalence (cong α) (λ where refl → refl)

 ⇒-equivalence : {σ₁ σ₂ τ₁ τ₂ : Type A} →
                 (σ₁ ≡ σ₂ × τ₁ ≡ τ₂) ⇔ (σ₁ ⇒ τ₁ ≡ σ₂ ⇒ τ₂)
 ⇒-equivalence = equivalence (uncurry (cong₂ _⇒_)) (λ where refl → refl , refl)

 eqdecType : Decidable {A = A} _≡_ → Decidable {A = Type A} _≡_
 eqdecType eq (α a₁)    (α a₂)    = RNDec.map α-equivalence (eq a₁ a₂)
 eqdecType eq (σ₁ ⇒ τ₁) (σ₂ ⇒ τ₂) = RNDec.map ⇒-equivalence (eqdecType eq σ₁ σ₂ ×-dec eqdecType eq τ₁ τ₂)
 eqdecType eq (α _)     (_ ⇒ _)   = no (λ ())
 eqdecType eq (_ ⇒ _)   (α _)     = no (λ ())

data `Bidi (P : Set) : Set where
  Cut App Lam Emb : `Bidi P
  Let : {p : P} → `Bidi P

-- Throwing in some useful combinators

module _ {I : Set} where

  `κ_`×_ : Set → Desc I → Desc I
  `κ A `× d = `σ A $ const d

  Located : Desc I → Desc I
  Located d = `κ Position `× d

module Surface where

-- I'm adding useless `κ_`×_ parts to keep the layout the
-- same between surface and internal. This will allow us to
-- use the same pattern synonyms for both!
  surface : Set → Desc Mode
  surface A = Located $ `σ (`Bidi ⊤) $ λ where
    Cut → `κ Type A `× `X [] Check (`∎ Infer)
    App → `κ ⊤      `× `X [] Infer (`X [] Check (`∎ Infer))
    Lam → `κ ⊤      `× `X (Infer ∷ []) Check (`∎ Check)
    Let → `κ ⊤      `× `X [] Infer (`X (Infer ∷ []) Check (`∎ Check))
    Emb → `κ ⊤      `× `X [] Infer (`∎ Check)

  Parsed : Mode → Set
  Parsed = Raw Position (surface String) _

  Scoped : Mode → List Mode → Set
  Scoped = Tm (surface ℕ) _


module Internal where

  internal : (P : Set) → Desc (Mode × Type ℕ)
  internal P = Located $ `σ (`Bidi P) $ λ where
    Cut → `σ (Type ℕ)          $ λ σ →
          `X [] (Check , σ) (`∎ (Infer , σ))
    App → `σ (Type ℕ × Type ℕ) $ uncurry $ λ σ τ →
          `X [] (Infer , σ ⇒ τ) (`X [] (Check , σ) (`∎ (Infer , τ)))
    Lam → `σ (Type ℕ × Type ℕ) $ uncurry $ λ σ τ →
          `X ((Infer , σ) ∷ []) (Check , τ) (`∎ (Check , σ ⇒ τ))
    Let → `σ (Type ℕ × Type ℕ) $ uncurry $ λ σ τ →
          `X [] (Infer , σ) (`X ((Infer , σ) ∷ []) (Check , τ) (`∎ (Check , τ)))
    Emb → `σ (Type ℕ)          $ λ σ →
          `X [] (Infer , σ) (`∎ (Check , σ))

  Internal : (P : Set) → (Mode × Type ℕ) ─Scoped
  Internal P = Tm (internal P) _

  typed = internal ⊤

  Typed : (Mode × Type ℕ) ─Scoped
  Typed = Tm typed _

  letfree = internal ⊥

  LetFree : (Mode × Type ℕ) ─Scoped
  LetFree = Tm letfree _

  erase : ∀ {X σ Γ} → ⟦ letfree ⟧ X σ Γ → ⟦ typed ⟧ X σ Γ
  erase (r , Cut , p) = r , Cut , p
  erase (r , App , p) = r , App , p
  erase (r , Lam , p) = r , Lam , p
  erase (r , Emb , p) = r , Emb , p
  erase (r , Let {} , p)

  data LetView {X Γ} : ∀ {σ} → ⟦ typed ⟧ X σ Γ → Set where
    Let  : ∀ r {σ τ} e b → LetView (r , Let , (σ , τ) , e , b , refl)
    ¬Let : ∀ {σ} (t : ⟦ letfree ⟧ X σ Γ) → LetView (erase t)

  letView : ∀ {X Γ σ} (t : ⟦ typed ⟧ X σ Γ) → LetView t
  letView (r , Cut , p)                = ¬Let (r , Cut , p)
  letView (r , App , p)                = ¬Let (r , App , p)
  letView (r , Lam , p)                = ¬Let (r , Lam , p)
  letView (r , Emb , p)                = ¬Let (r , Emb , p)
  letView (r , Let , _ , e , b , refl) = Let r e b

-- Traditional pattern synonyms (usable on the LHS only)
pattern _`∶'_      t σ = (Cut , σ , t , refl)
pattern _`∶_       t σ = `con (_ , t `∶' σ)
pattern _`$'_      f t = (App , _ , f , t , refl)
pattern _`$_       f t = `con (_ , f `$' t)
pattern `λ'_       b   = (Lam , _ , b , refl)
pattern `λ_        b   = `con (_ , `λ' b)
pattern `let'_`in_ e b = (Let , _ , e , b , refl)
pattern `let_`in_  e b = `con (_ , `let' e `in b)
pattern `-'        t   = (Emb , _ , t , refl)
pattern `-         t   = `con (_ , `-' t)

-- Position-aware pattern synonyms (usable both on the LHS and RHS)
pattern _>_`∶'_      r t σ = (r , Cut , σ , t , refl)
pattern _>_`∶_       r t σ = `con (r > t `∶' σ)
pattern _>_`$'_      r f t = (r , App , _ , f , t , refl)
pattern _>_`$_       r f t = `con (r > f `$' t)
pattern _>`λ'_       r b   = (r , Lam , _ , b , refl)
pattern _>`λ_        r b   = `con (r >`λ' b)
pattern _>`let'_`in_ r e b = (r , Let , _ , e , b , refl)
pattern _>`let_`in_  r e b = `con (r >`let' e `in b)
pattern _>`-'_       r t   = (r , Emb , _ , t , refl)
pattern _>`-_        r t   = `con (r >`-' t)

pattern _>`λ'_↦_       r x b   = (r , Lam , _ , (x ∷ [] , b) , refl)
pattern _>`λ_↦_        r x b   = `con (r >`λ' x ↦ b)
pattern _>`let'_↦_`in_ r x e b = (r , Let , _ , e , (x ∷ [] , b) , refl)
pattern _>`let_↦_`in_  r x e b = `con (r >`let' x ↦ e `in b)

-- Examples of terms of differnent languages using the same pattern synonyms
-- Here we use `start' as a placeholder for positions

_ : Surface.Scoped Check []
_ = start >`λ (start >`- `var z)

_ : ∀ {σ} → Internal.Typed (Check , σ ⇒ σ) []
_ = start >`λ (start >`- `var z)
