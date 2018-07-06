module Scopecheck where

open import Data.Product as Product
open import Data.Nat
open import Data.String as String
open import Data.Maybe as Maybe
open import Data.List using ([])
open import Data.List.All using ([])
open import Function

open import Category.Monad
open import Category.Monad.State

open import Generic.Syntax
open import Generic.AltSyntax

open import Text.Parser.Position

open import Language
open Surface
open import Types

-- Data.AVL is not quite usable with String at the moment IIRC
-- So instead I'm using a quick and dirty representation
import Data.Map as M

module Map = M.Map String._≟_ ℕ
open Map using (Map; RMap)

module _ where

  private M = State (Map × ℕ)
  open RawMonadState (StateMonadState (Map × ℕ))

  resolve : String → M ℕ
  resolve str = do
    (mp , gen) ← get
    case Map.assoc str mp of λ where
      (just n) → return n
      nothing  → do
        put (Map.set str gen mp , suc gen)
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

scopecheck : ∀ {m} → Parsed m → Result (Scoped m [] × RMap)
scopecheck r = Types.fromMaybe (At start OutOfScope "placeholder")
  $ let open RawMonad Maybe.monad in do
  t ← ScopeCheck.scopeCheck eqdecMode _ [] [] r
  let t′ = cleanupTerm t (Map.empty , 0)
  return $ map₂ (Map.invert ∘′ proj₁) t′
