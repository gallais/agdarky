module Scopecheck where

open import Data.Product as Product
open import Data.Nat
open import Data.String
open import Data.String.Unsafe as String
open import Data.Maybe.Base using (Maybe; nothing; just; maybe′)
open import Data.Sum.Base as Sum using (inj₁; inj₂; [_,_]′)
open import Data.List as List using ([])
open import Data.List.Relation.Unary.All as All using (All)
open import Data.List.Relation.Unary.All.Properties
open import Function

open import Category.Monad
open import Category.Monad.State

open import Generic.Syntax
open import Generic.AltSyntax

open import Text.Parser.Position

open import Language
open Surface
open import Types

module _ where

  M = State (Map × ℕ)
  open RawMonadState (StateMonadState (Map × ℕ)) hiding (_⊗_)

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
  cleanupType (σ ⊗ τ) = _⊗_ <$> cleanupType σ ⊛ cleanupType τ

  cleanupTerm : ∀ {i σ Γ} → Tm (surface String) i σ Γ → M (Scoped σ Γ)
  cleanupTerm (`var k)          = return $ `var k
  cleanupTerm (r >[ t `∶ σ ])   = r >[_`∶_] <$> cleanupTerm t ⊛ cleanupType σ
  cleanupTerm (r >[ f `$ t ])   = r >[_`$_] <$> cleanupTerm f ⊛ cleanupTerm t
  cleanupTerm (r >`fst b)       = r >`fst_  <$> cleanupTerm b
  cleanupTerm (r >`snd b)       = r >`snd_  <$> cleanupTerm b
  cleanupTerm (r >`λ b)         = r >`λ_  <$> cleanupTerm b
  cleanupTerm (r >[ a `, b ])   = r >[_`,_] <$> cleanupTerm a ⊛ cleanupTerm b
  cleanupTerm (r >`let e `in b) = r >`let_`in_ <$> cleanupTerm e ⊛ cleanupTerm b
  cleanupTerm (r >`- t)         = r >`-_  <$> cleanupTerm t

open RawMonad (Compiler.monad String)
open Compiler
open ScopeCheck

scopecheck : ∀ {Σ m} (p : Definitions Σ) → Parsed m →
             Compiler String (Scoped m (modes p))
scopecheck p r = do
  let scopeError = uncurry At_OutOfScope_
  t  ← liftResult $ Sum.map₁ scopeError $ scopeCheck eqdecMode _ _ (names p) r
  liftState $ cleanupTerm t
