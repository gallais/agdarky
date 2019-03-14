module Parse where

open import Data.Nat.Properties using (≤-refl)
open import Data.Empty
open import Data.Product

open import Data.String as String
open import Data.Sum.Base using (inj₁; inj₂)
open import Data.List.Base using ([])

open import Function

open import Category.Monad

open import Induction.Nat.Strong as INS

open import Data.Subset
open import Data.List.Sized.Interface
open import Relation.Binary.PropositionalEquality.Decidable
open import Relation.Unary using (IUniversal)

open import Text.Parser.Types
open import Text.Parser.Position using (start)
open import Text.Parser.Combinators hiding (_>>=_)
open import Text.Parser.Combinators.Char
open import Text.Parser.Monad

open import Generic.AltSyntax

open import Language
open Surface
open import Types

module ParserM = Agdarsec Error ⊥ (record { into = At_ParseError ∘′ proj₁ })
open ParserM

instance
  _ = ParserM.monadZero
  _ = ParserM.monadPlus
  _ = ParserM.monad

P = ParserM.chars

type : ∀[ Parser P (Type String) ]
type = fix _ $ λ rec →
  let name = String.fromList⁺ <$> (char '`' &> box alphas⁺) in
  chainr1 (α <$> name <|> parens rec)
          (box (_⇒_ <$ withSpaces (char '→')))

record Bidirectional n : Set where
  field infer : Parser P (Parsed Infer) n
        check : Parser P (Parsed Check) n
open Bidirectional

bidirectional : ∀[ Bidirectional ]
bidirectional = fix Bidirectional $ λ rec →
  let □check = INS.map check rec
      name   = fromList⁺ <$> alphas⁺
      var    = `var <$> name
      cut    = (λ where ((c , p) , σ) → p > c `∶ σ)
              <$> ((char '(' &> INS.map commit □check)
              <&> box (getPosition <M& withSpaces (char ':'))
              <&> box type)
              <&  box (char ')')
      app    = _>_`$_ <$> (space &M> getPosition)
      infer  = hchainl (var <|> cut) (box app) □check
      lam    = (λ where ((p , x) , c) → p >`λ x ↦ c)
              <$> ((char 'λ' &> box (getPosition <M&> withSpaces name))
              <&> box ((char '.') <&? box spaces &> INS.map commit □check))
      emb    = (uncurry _>`-_) <$> (getPosition <M&> infer)
      check  = lam <|> emb
  in record { infer = infer ; check = check }

parse : String → Types.Result (Parsed Infer)
parse str = result inj₁ inj₁ (inj₂ ∘′ Success.value ∘′ proj₁)
   $′ runParser (infer bidirectional) ≤-refl (String.toVec str) (start , [])
   where module M = RawMonad ParserM.monad

open import Agda.Builtin.Equality

_ : parse "(λ x . 1 : `a → `a)" ≡ inj₁ (At record { line = 0 ; offset = 8 } ParseError)
_ = refl
