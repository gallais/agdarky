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
open import Generic.Syntax using (`var)
open import Language; open Surface
open import Types
open import Parse
open import Scopecheck
open import Typecheck
open import LetInline
open import Print

open import Category.Monad

open RawMonad (Compiler.monad String)
open Compiler

declarations : List (String × Type String × Parsed Check) →
               ∀ {Γ} → Definitions Γ → Compiler String (∃ Definitions)
declarations []             p = pure $ -, p
declarations ((str , sig , decl) ∷ decls) p = do
  scoped ← scopecheck p decl
  σ      ← liftState $ cleanupType sig
  typed  ← ppCompiler $ liftResult $ type- Check _ scoped (map⁺ self) σ
  let x = str ∶ σ ≔ subst (Internal.Typed _) (eq^fromTyping _) typed
  declarations decls (p & x)

declaration : Parsed Infer → ∀ {Γ} → Definitions Γ →
              Compiler String (∃ λ σ → Expression σ Γ)
declaration d {Γ} p = do
  scoped      ← scopecheck p d
  (σ , typed) ← ppCompiler $ liftResult $ type- Infer Γ scoped (map⁺ self)
  pure (σ , subst (Internal.Typed _) (eq^fromTyping _) typed)

pipeline : String → Error String ⊎ Program
pipeline str = Compiler.run $ do
  (decls , expr) ← liftResult $ parse str
  (Γ , defs)     ← declarations (List⁺.toList decls) []
  (σ , eval)     ← declaration expr defs
  pure $ assuming defs have eval

open import Agda.Builtin.Equality

_ : from-inj₂ (pipeline "def id  : 'a → 'a = λx. x
\            \def snd : 'a → 'b → 'b = λx. λy.y
\            \eval id")
  ≡ assuming []
  & "id"  ∶ α 0 ⇒ α 0       ≔ `λ `- `var z
  & "snd" ∶ α 0 ⇒ α 1 ⇒ α 1 ≔ `λ `λ `- `var z
  have `var (s z)
_ = refl
