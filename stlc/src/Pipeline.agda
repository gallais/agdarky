module Pipeline where

open import Data.Product
open import Data.String
open import Data.Sum
open import Data.List.Base as List
import Data.List.NonEmpty as List⁺
open import Data.List.Relation.Unary.All
open import Data.List.Relation.Unary.All.Properties
open import Text.Parser.Position
open import Function
open import Relation.Binary.PropositionalEquality

open import var using (z; s)
import environment as E
open import Generic.Syntax using (`var)
open import Generic.Semantics.Syntactic using (sub)
open import Language; open Surface
open import Types
open import Parse
open import Scopecheck
open import Typecheck
open import LetInline
open import Eval
open import Print

open import Category.Monad

open Compiler

module _ where

  open RawMonad (Compiler.monad String)

  declarations : List (Position × String × Type String × Parsed Check) →
                 ∀ {Γ} → Definitions Γ → Compiler String (∃ Definitions)
  declarations []                               p = pure $ -, p
  declarations ((r , str , sig , decl) ∷ decls) p = do
    scoped ← scopecheck p decl
    σ      ← liftState $ cleanupType sig
    typed  ← ppCompiler $ liftResult $ type- Check _ scoped (map⁺ self) σ
    let x = r > str ∶ σ ≔ subst (Internal.Typed _) (eq^fromTyping _) typed
    declarations decls (p & x)

  declaration : Parsed Infer → ∀ {Γ} → Definitions Γ →
                Compiler String (∃ λ σ → Expression σ Γ)
  declaration d {Γ} p = do
    scoped      ← scopecheck p d
    (σ , typed) ← ppCompiler $ liftResult $ type- Infer Γ scoped (map⁺ self)
    pure (σ , subst (Internal.Typed _) (eq^fromTyping _) typed)

  toProgram : String → Compiler String Program
  toProgram str = do
    (decls , expr) ← liftResult $ parse str
    (Γ , defs)     ← declarations (List⁺.toList decls) []
    (σ , eval)     ← declaration expr defs
    pure $ assuming defs have eval

  pipeline : String → Error String ⊎ (String × String × String)
  pipeline str = Compiler.run $ do
    (decls , expr) ← liftResult $ parse str
    (Γ , defs)     ← declarations (List⁺.toList decls) []
    (σ , eval)     ← declaration expr defs
    let lets   = toLets defs (toCheck eval)
    let unlets = let-inline lets
    let val    = norm unlets
    m ← getMap
    let rm = Map.invert m
    pure $ print lets rm
         , print unlets rm
         , print val rm

open import Agda.Builtin.Equality

_ : Compiler.run (toProgram "def id  : 'a → 'a = λx. x
\            \def deux : 'a → 'b → 'b = λx. λy.y
\            \have id")
  ≡ inj₂ (assuming []
  & "id"   ∶ α 0 ⇒ α 0       ≔ `λ `- `var z
  & "deux" ∶ α 0 ⇒ α 1 ⇒ α 1 ≔ `λ `λ `- `var z
  have `var (s z))
_ = refl

-- normalisation test

_ : pipeline "def idh : ('a → 'a) → ('a → 'a) = λf.λx. f x
\            \def id : ('a → 'a) = λx.x
\            \have idh id"
  ≡ inj₂ ("let c = (λa.λb.a b : (`a → `a) → `a → `a) in \
          \let e = (λd.d : `a → `a) in \
          \c e"
         , "(λa.λb.a b : (`a → `a) → `a → `a) (λc.c : `a → `a)"
         , "λa.a")
_ = refl
