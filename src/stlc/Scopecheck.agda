module Scopecheck where

open import Data.Product as Product
open import Data.Nat
open import Data.String
open import Data.String.Unsafe as String
open import Data.Maybe.Base using (Maybe; nothing; just; maybe′)
open import Data.Sum.Base as Sum using (inj₁; inj₂; [_,_]′)
open import Data.List using ([])
open import Data.List.Relation.Unary.All using ([])
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
  cleanupTerm (`var k)          = return $ `var k
  cleanupTerm (r > t `∶ σ)      = r >_`∶_ <$> cleanupTerm t ⊛ cleanupType σ
  cleanupTerm (r > f `$ t)      = r >_`$_ <$> cleanupTerm f ⊛ cleanupTerm t
  cleanupTerm (r >`λ b)         = r >`λ_  <$> cleanupTerm b
  cleanupTerm (r >`let e `in b) = r >`let_`in_ <$> cleanupTerm e ⊛ cleanupTerm b
  cleanupTerm (r >`- t)         = r >`-_  <$> cleanupTerm t

open RawMonad Result.monad

scopecheck : ∀ {m} → Parsed m → Result (Scoped m [] × RMap)
scopecheck r = do
  t ← Sum.map error id $ ScopeCheck.scopeCheck eqdecMode pos? _ [] [] r
  let (t′ , mp , _) = cleanupTerm t (Map.empty , 0)
  pure $ t′ , Map.invert mp

  where

    error : String × Maybe Position → Error
    error (str , mp) = maybe′ (At_OutOfScope str) (At start OutOfScope str) mp

    pos? : ∀ σ → Raw (surface String) _ σ → Maybe Position
    pos? _ (`var _)       = nothing
    pos? _ (`con (r , _)) = just r
