module Language where

open import Data.Unit
open import Data.Empty
open import Data.Product as Prod
open import Data.Nat
open import Data.List as List using (List; []; _∷_)
open import Data.List.Relation.Unary.All -- important for the pattern synonyms!
open import Data.String as String using (String; _++_)
open import Function
open import Function.Equivalence
open import Relation.Nullary
open import Relation.Nullary.Decidable as RNDec
open import Relation.Nullary.Product
open import Relation.Binary using (Decidable)
open import Relation.Binary.PropositionalEquality

open import var using (z; s; _─Scoped)
open import environment
open import Generic.Syntax
open import Generic.AltSyntax
open import Generic.Semantics.Syntactic using (sub)
open import Text.Parser.Position as Position using (Position; _∶_; start)

infixr 6 _⇒_
infixr 7 _⊗_
data Type (A : Set) : Set where
  α   : A → Type A
  _⊗_ : (σ τ : Type A) → Type A
  _⇒_ : (σ τ : Type A) → Type A

show  : Type String → String
pshow : Type String → String

show (α str) = "'" ++ str
show (σ ⊗ τ) = pshow σ ++ " * " ++ show τ
show (σ ⇒ τ) = pshow σ ++ " → " ++ show τ

pshow σ@(α _)   = show σ
pshow σ@(_ ⊗ _) = "(" ++ show σ ++ ")"
pshow σ@(_ ⇒ _) = "(" ++ show σ ++ ")"

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

  ⊗-equivalence : {σ₁ σ₂ τ₁ τ₂ : Type A} →
                  (σ₁ ≡ σ₂ × τ₁ ≡ τ₂) ⇔ (σ₁ ⊗ τ₁ ≡ σ₂ ⊗ τ₂)
  ⊗-equivalence = equivalence (uncurry (cong₂ _⊗_)) (λ where refl → refl , refl)

module _ {A : Set} (eq : Decidable {A = A} _≡_) where

  eqdecType : Decidable {A = Type A} _≡_
  eqdecType (α a₁)    (α a₂)    = RNDec.map α-equivalence (eq a₁ a₂)
  eqdecType (σ₁ ⊗ τ₁) (σ₂ ⊗ τ₂) =
    RNDec.map ⊗-equivalence (eqdecType σ₁ σ₂ ×-dec eqdecType τ₁ τ₂)
  eqdecType (σ₁ ⇒ τ₁) (σ₂ ⇒ τ₂) =
    RNDec.map ⇒-equivalence (eqdecType σ₁ σ₂ ×-dec eqdecType τ₁ τ₂)

  eqdecType (α _)     (_ ⇒ _)   = no (λ ())
  eqdecType (_ ⇒ _)   (α _)     = no (λ ())
  eqdecType (α _) (_ ⊗ _) = no (λ ())
  eqdecType (_ ⊗ _) (α _) = no (λ ())
  eqdecType (_ ⊗ _) (_ ⇒ _) = no (λ ())
  eqdecType (_ ⇒ _) (_ ⊗ _) = no (λ ())

data `Bidi (P : Set) : Set where
  Cut App Fst Snd : `Bidi P
  Lam Prd Emb     : `Bidi P
  Let             : {p : P} → `Bidi P

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
    Fst → `κ ⊤      `× `X [] Infer (`∎ Infer)
    Snd → `κ ⊤      `× `X [] Infer (`∎ Infer)
    Lam → `κ ⊤      `× `X (Infer ∷ []) Check (`∎ Check)
    Prd → `κ ⊤      `× `X [] Check (`X [] Check (`∎ Check))
    Emb → `κ ⊤      `× `X [] Infer (`∎ Check)
    Let → `κ ⊤      `× `X [] Infer (`X (Infer ∷ []) Check (`∎ Check))


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
    Fst → `σ (Type ℕ × Type ℕ) $ uncurry $ λ σ τ →
          `X [] (Infer , σ ⊗ τ) (`∎ (Infer , σ))
    Snd → `σ (Type ℕ × Type ℕ) $ uncurry $ λ σ τ →
          `X [] (Infer , σ ⊗ τ) (`∎ (Infer , τ))
    Lam → `σ (Type ℕ × Type ℕ) $ uncurry $ λ σ τ →
          `X ((Infer , σ) ∷ []) (Check , τ) (`∎ (Check , σ ⇒ τ))
    Prd → `σ (Type ℕ × Type ℕ) $ uncurry $ λ σ τ →
          `X [] (Check , σ) (`X [] (Check , τ) (`∎ (Check , σ ⊗ τ)))
    Emb → `σ (Type ℕ)          $ λ σ →
          `X [] (Infer , σ) (`∎ (Check , σ))
    Let → `σ (Type ℕ × Type ℕ) $ uncurry $ λ σ τ →
          `X [] (Infer , σ) (`X ((Infer , σ) ∷ []) (Check , τ) (`∎ (Check , τ)))

  Internal : (P : Set) → (Mode × Type ℕ) ─Scoped
  Internal P = Tm (internal P) _

  getPosition : ∀ {P σ Γ} → Internal P σ Γ → Position
  getPosition (`var _)       = start
  getPosition (`con (r , _)) = r

  typed = internal ⊤

  Typed : (Mode × Type ℕ) ─Scoped
  Typed = Tm typed _

  letfree = internal ⊥

  LetFree : (Mode × Type ℕ) ─Scoped
  LetFree = Tm letfree _

  erase : ∀ {X σ Γ} → ⟦ letfree ⟧ X σ Γ → ⟦ typed ⟧ X σ Γ
  erase (r , Cut , p) = r , Cut , p
  erase (r , App , p) = r , App , p
  erase (r , Fst , p) = r , Fst , p
  erase (r , Snd , p) = r , Snd , p
  erase (r , Lam , p) = r , Lam , p
  erase (r , Emb , p) = r , Emb , p
  erase (r , Prd , p) = r , Prd , p
  erase (r , Let {} , p)

  data LetView {X Γ} : ∀ {σ} → ⟦ typed ⟧ X σ Γ → Set where
    Let  : ∀ r {σ τ} e b → LetView (r , Let , (σ , τ) , e , b , refl)
    ¬Let : ∀ {σ} (t : ⟦ letfree ⟧ X σ Γ) → LetView (erase t)

  letView : ∀ {X Γ σ} (t : ⟦ typed ⟧ X σ Γ) → LetView t
  letView (r , Cut , p)                = ¬Let (r , Cut , p)
  letView (r , App , p)                = ¬Let (r , App , p)
  letView (r , Fst , p)                = ¬Let (r , Fst , p)
  letView (r , Snd , p)                = ¬Let (r , Snd , p)
  letView (r , Lam , p)                = ¬Let (r , Lam , p)
  letView (r , Emb , p)                = ¬Let (r , Emb , p)
  letView (r , Prd , p)                = ¬Let (r , Prd , p)
  letView (r , Let , _ , e , b , refl) = Let r e b

-- Traditional pattern synonyms (usable on the LHS only)
pattern _`∶'_      t σ = (Cut , σ , t , refl)
pattern _`∶_       t σ = `con (_ , t `∶' σ)
pattern _`$'_      f t = (App , _ , f , t , refl)
pattern _`$_       f t = `con (_ , f `$' t)
pattern `fst'_     e   = (Fst , _ , e , refl)
pattern `fst_      e   = `con (_ , `fst' e)
pattern `snd'_     e   = (Snd , _ , e , refl)
pattern `snd_      e   = `con (_ , `snd' e)
pattern `λ'_       b   = (Lam , _ , b , refl)
pattern `λ_        b   = `con (_ , `λ' b)
pattern `λ'_↦_     x b  = (_ , Lam , _ , (x ∷ [] , b) , refl)
pattern `λ_↦_       x b = `con (`λ' x ↦ b)
pattern _`,'_      a b  = (Prd , _ , a , b , refl)
pattern _`,_       a b  = `con (_ , a `,' b)
pattern `let'_`in_ e b = (Let , _ , e , b , refl)
pattern `let_`in_  e b = `con (_ , `let' e `in b)
pattern `-'_        t   = (Emb , _ , t , refl)
pattern `-_         t   = `con (_ , `-' t)

-- Position-aware pattern synonyms (usable both on the LHS and RHS)
pattern _>[_`∶'_]    r t σ = (r , Cut , σ , t , refl)
pattern _>[_`∶_]     r t σ = `con (r >[ t `∶' σ ])
pattern _>[_`$'_]    r f t = (r , App , _ , f , t , refl)
pattern _>[_`$_]     r f t = `con (r >[ f `$' t ])
pattern _>`fst'_     r e   = (r , Fst , _ , e , refl)
pattern _>`fst_      r e   = `con (r >`fst' e)
pattern _>`snd'_     r e   = (r , Snd , _ , e , refl)
pattern _>`snd_      r e   = `con (r >`snd' e)
pattern _>`λ'_       r b   = (r , Lam , _ , b , refl)
pattern _>`λ_        r b   = `con (r >`λ' b)
pattern _>[_`,'_]    r a b = (r , Prd , _ , a , b , refl)
pattern _>[_`,_]     r a b  = `con (r >[ a `,' b ])
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

toCheck : ∀ {m σ Γ} → Internal.Typed (m , σ) Γ → Internal.Typed (Check , σ) Γ
toCheck {Infer} t = Internal.getPosition t >`- t
toCheck {Check} t = t

toInfer : ∀ {m σ Γ} → Internal.Typed (m , σ) Γ → Internal.Typed (Infer , σ) Γ
toInfer {Infer} t = t
toInfer {Check} t = Internal.getPosition t >[ t `∶ _ ]

infersOf : List (Type ℕ) → List (Mode × Type ℕ)
infersOf = List.map (Infer ,_)

data Definitions : List (Type ℕ) → Set
record Definition {ds} (p : Definitions ds) : Set

infixl 11 _>_∶_≔_ _∶_≔_
record Definition {ds} p where
  constructor _>_∶_≔_
  field pos  : Position
        name : String
        type : Type ℕ
        term : Internal.Typed (Check , type) (infersOf ds)

pattern _∶_≔_ x σ t = _ > x ∶ σ ≔ t

infixl 10 _&_
data Definitions where
  []  : Definitions []
  _&_ : ∀ {ds} (p : Definitions ds) (d : Definition p) →
        Definitions (Definition.type d ∷ ds)

modes : ∀ {Γ} → Definitions Γ → List Mode
modes {Γ} _ = List.map (const Infer) Γ

names : ∀ {Γ} (ds : Definitions Γ) → All (const String) (modes ds)
names []       = []
names (ds & d) = Definition.name d ∷ names ds

toEnv : ∀ {Γ} → Definitions Γ → (infersOf Γ ─Env) Internal.Typed []
toEnv []                  = ε
toEnv (Γ & r > _ ∶ σ ≔ d) = let ρ = toEnv Γ in ρ ∙ sub ρ (r >[ d `∶ σ ])

Expression : Type ℕ ─Scoped
Expression σ Γ = Internal.Typed (Infer , σ) (infersOf Γ)


toLets : ∀ {σ Γ} → Definitions Γ →
         Internal.Typed (Check , σ) (infersOf Γ) → Internal.Typed (Check , σ) []
toLets []       e = e
toLets (ds & d) e = toLets ds $ Definition.pos d
                              >`let toInfer (Definition.term d)
                              `in e

infix 9 _&&_
data Program : Set where
  _&&_ : ∀ {σ Γ} → Definitions Γ → Expression σ Γ → Program

pattern assuming_have_ defs expr = defs && expr

{-
-- Can't quite write this: we would have to also write down the position of each node

_ : Program
_ = let nat = α 0 ⇒ (α 0 ⇒ α 0) ⇒ α 0 in assuming []
  & "id"   ∶ nat ⇒ nat ≔ `λ `- `var z
  & "zero" ∶ nat       ≔ `λ `λ `- `var (s z)
  & "suc"  ∶ nat ⇒ nat ≔ `λ `λ `λ `- (`var z
                         `$ (`- ((`var (s (s z))
                         `$ (`- (`var (s z))))
                         `$ (`- (`var z)))))
    have `var (s (s z)) `$ (`- (`var z `$ (`- (`var z `$ (`- `var (s z))))))
-}
