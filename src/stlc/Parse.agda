module Parse where

import Level
open import Data.Nat hiding (_>_)
open import Data.Empty
open import Data.Product hiding (,_)
open import Data.Char
open import Data.String as String
open import Data.Sum
open import Data.Sum.Categorical
open import Data.List hiding ([_])
open import Data.List.All
open import Data.List.NonEmpty as NE hiding ([_])
open import Data.List.Sized
open import Data.Maybe
open import Data.Vec hiding ([_] ; _>>=_)
open import Function
open import Relation.Binary.PropositionalEquality hiding ([_])

open import Category.Monad
open import Category.Monad.State

open import Induction.Nat.Strong as INS

open import Data.Subset
open import Relation.Binary.PropositionalEquality.Decidable
open import Relation.Unary.Indexed
open import Text.Parser.Types
open import Text.Parser.Instruments
open import Text.Parser.Position
import Text.Parser.Success as S
open import Text.Parser.Combinators hiding (_>>=_)
open import Text.Parser.Char

open import Generic.AltSyntax

open import Language
open Surface

private M = StateT Position (Position ⊎_)

P : Parameters
Parameters.Tok  P = Char
Parameters.Toks P = Vec Char
Parameters.Pos  P = Position
Parameters.Ann  P = ⊥
Parameters.M    P = StateT Position (Position ⊎_)

instance

  instrP : Instrumented P
  withAnnotation instrP = λ _ ma → ma
  recordToken    instrP = λ c p → inj₂ (_ , next c p)
  getPosition    instrP = λ p → inj₂ (p , p)
  getAnnotation  instrP = λ p → inj₂ (nothing , p)

  monad-M : RawMonad M
  monad-M = record
    { return = λ a p → inj₂ (a , p)
    ; _>>=_  = λ ma f p → [ inj₁ , uncurry f ]′ (ma p)
    }

  monad0-M : RawMonadZero M
  monad0-M = record { monad = monad-M ; ∅ = inj₁ }

  monad+-M : RawMonadPlus M
  monad+-M = record
    { monadZero = monad0-M
    ; _∣_       = λ ma₁ ma₂ p → [ const (ma₂ p) , inj₂ ]′ (ma₁ p)
    }

type : [ Parser P (Type String) ]
type = fix _ $ λ rec →
  let name = String.fromList⁺ <$> (char '`' &> box alphas⁺) in
  chainr1 (α <$> name <|> parens rec)
          (box $ _⇒_ <$ withSpaces (char '→'))

record Bidirectional (n : ℕ) : Set where
  field infer : Parser P (Parsed Infer) n
        check : Parser P (Parsed Check) n
open Bidirectional

module ST = RawMonadState (StateTMonadState Position (monadₗ Position Level.zero))

prePosition : ∀ {A} → [ Parser P A ⟶ Parser P (Position × A) ]
runParser (prePosition a) m≤n toks = let open ST in do
  p ← get
  S.map (p ,_) ST.<$> runParser a m≤n toks

postPosition : ∀ {A} → [ Parser P A ⟶ Parser P (A × Position) ]
runParser (postPosition a) m≤n toks = let open ST in do
  a ← runParser a m≤n toks
  p ← get
  pure $ S.map (_, p) a

bidirectional : [ Bidirectional ]
bidirectional = fix Bidirectional $ λ rec →
  let □check = INS.map check rec
      name   = fromList⁺ <$> alphas⁺
      var    = `var <$> name
      cut    = (λ where ((c , p) , σ) → p > c `∶ σ)
              <$> ((char '(' &> □check)
              <&> box (proj₂ <$> postPosition (char ':'))
              <&> box type)
              <&  box (char ')')
      app    = _>_`$_ ∘ proj₂ <$> postPosition space
      infer  = hchainl (var <|> cut) (box app) □check
      lam    = (λ where ((p , x) , c) → p >`λ x ↦ c)
              <$> ((char 'λ' &> box (prePosition (withSpaces name)))
              <&> box ((char '.') <&? box spaces &> □check))
      emb    = (uncurry _>`-_) <$> (prePosition infer)
      check  = lam <|> emb
  in record { infer = infer ; check = check }

parse : ∀ m → [ Parser P (Parsed m) ]
parse Infer = infer bidirectional
parse Check = check bidirectional
