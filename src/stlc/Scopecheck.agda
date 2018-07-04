module Scopecheck where

open import Data.Product
open import Data.Nat
open import Data.String as String
open import Data.Maybe as Maybe
open import Data.List
open import Data.List.All using ([])
open import Function
open import Relation.Nullary

open import Category.Monad
open import Category.Monad.State

open import Generic.Syntax
open import Generic.AltSyntax

open import Language
open Surface

-- Data.AVL is not quite usable with String at the moment IIRC
-- So instead I'm using a quick and dirty representation
module Map where

  Map = String → Maybe ℕ

  empty : Map
  empty = const nothing

  set : String → ℕ → Map → Map
  set str n mp str′ with str String.≟ str′
  ... | yes _ = just n
  ... | no  _ = mp str′

module _ where

  open Map

  M = State (Map × ℕ)
  open RawMonadState (StateMonadState (Map × ℕ))

  resolve : String → M ℕ
  resolve str = do
    (mp , gen) ← get
    case mp str of λ where
      (just n) → return n
      nothing  → do
        put (set str gen mp , suc gen)
        return gen

  cleanupType : Type String → M (Type ℕ)
  cleanupType (α str) = α <$> resolve str
  cleanupType (σ ⇒ τ) = _⇒_ <$> cleanupType σ ⊛ cleanupType τ

  cleanupTerm : ∀ {i σ Γ} → Tm (surface String) i σ Γ → M (Scoped σ Γ)
  cleanupTerm (`var k)     = return $ `var k
  cleanupTerm (r > t `∶ σ) = r >_`∶_ <$> cleanupTerm t ⊛ cleanupType σ
  cleanupTerm (r > f `$ t) = r >_`$_ <$> cleanupTerm f ⊛ cleanupTerm t
  cleanupTerm (r >`λ b)    = r >`λ_  <$> cleanupTerm b
  cleanupTerm (r >`- t)    = r >`-_  <$> cleanupTerm t

scopecheck : ∀ {m} → Parsed m → Maybe (Scoped m [])
scopecheck r = let open RawMonad Maybe.monad in do
  t ← ScopeCheck.scopeCheck eqdecMode _ [] [] r
  return $ proj₁ $ cleanupTerm t (Map.empty , 0)
