module Parse where

open import Level
open import Data.Unit using (⊤)
open import Data.Bool.Base using (Bool; true; false)
open import Data.Nat.Properties using (≤-refl)
open import Data.Empty
open import Data.Product

open import Data.Maybe
open import Data.Bool using (if_then_else_)
open import Data.Char as Char
open import Data.String as String
import Data.String.Unsafe as String
open import Data.Sum.Base using (_⊎_; inj₁; inj₂; [_,_]′)
open import Data.List.Base as List using (List; []; _∷_)
open import Data.List.NonEmpty as List⁺ using (List⁺; _∷_)
open import Data.Vec as Vec using (Vec)
open import Function

open import Category.Monad

open import Induction.Nat.Strong as INS

open import Data.Subset
open import Data.List.Sized.Interface
open import Relation.Binary using (Decidable)
open import Relation.Binary.PropositionalEquality
open import Relation.Binary.PropositionalEquality.Decidable
open import Relation.Nullary
open import Relation.Nullary.Decidable using (map′)
open import Relation.Unary using (IUniversal) renaming (_⇒_ to _⟶_)

open import Text.Parser.Types
open import Text.Parser.Position
open import Text.Parser.Combinators hiding (_>>=_)
open import Text.Parser.Monad

open import Generic.AltSyntax

open import Language
open Surface
open import Types

module ParserM = Agdarsec Error ⊥ (record { into = At_ParseError ∘′ proj₁ })
open ParserM

data Tok : Set where
  ID            : String → Tok
  ARR           : Tok
  LET EQ IN     : Tok
  LAM DOT       : Tok
  LPAR COL RPAR : Tok

_≟_ : Decidable {A = Tok} _≡_
ID x ≟ ID y = map′ (cong ID) (λ where refl → refl) (x String.≟ y)
ARR  ≟ ARR  = yes refl
LET  ≟ LET  = yes refl
EQ   ≟ EQ   = yes refl
IN   ≟ IN   = yes refl
LAM  ≟ LAM  = yes refl
DOT  ≟ DOT  = yes refl
LPAR ≟ LPAR = yes refl
COL  ≟ COL  = yes refl
RPAR ≟ RPAR = yes refl
_    ≟ _    = no p where postulate p : _

Token : Set
Token = Position × Tok

keywords : List⁺ (String × Tok)
keywords = ("→"   , ARR)
         ∷ ("λ"   , LAM)
         ∷ (":"   , COL)
         ∷ ("let" , LET)
         ∷ ("in"  , IN)
         ∷ []

breaking : Char → ∃ λ b → if b then Maybe Tok else Lift _ ⊤
breaking c = case c of λ where
  '(' → true , just LPAR
  ')' → true , just RPAR
  '.' → true , just DOT
  '=' → true , just EQ
  c   → if isSpace c then true , nothing else false , _

open import Text.Lexer keywords breaking ID using (tokenize)

instance
  _ = ParserM.monadZero
  _ = ParserM.monadPlus
  _ = ParserM.monad

P = ParserM.param Token (Vec Token) λ where (p , _) _ → Value (_ , p , [])

theTok : Tok → ∀[ Parser P Token ]
theTok t = maybeTok $ λ where
  tok@(p , t') → case t ≟ t' of λ where
    (yes eq) → just tok
    (no ¬eq) → nothing

name : ∀[ Parser P String ]
name = maybeTok λ where (p , ID str) → just str; _ → nothing

parens : ∀ {A} → ∀[ □ Parser P A ⟶ Parser P A ]
parens □p = theTok LPAR &> □p <& box (theTok RPAR)

type : ∀[ Parser P (Type String) ]
type = fix _ $ λ rec →
  let varlike str = case String.toList str of λ where
        ('`' ∷ nm) → just (String.fromList nm)
        _ → nothing
  in chainr1 (α <$> guardM varlike name <|> parens rec)
             (box (_⇒_ <$ theTok ARR))

record Bidirectional n : Set where
  field infer : Parser P (Parsed Infer) n
        check : Parser P (Parsed Check) n
open Bidirectional

bidirectional : ∀[ Bidirectional ]
bidirectional = fix Bidirectional $ λ rec →
  let □check = INS.map check rec
      □infer = INS.map infer rec
      var    = uncurry `var <$> (getPosition <M&> guard (List.all isAlpha ∘′ toList) name)
      cut    = (λ where ((t , (p , _)) , σ) → p > t `∶ σ)
               <$> (theTok LPAR
                &> □check <&> box (theTok COL) <&> box (commit type)
               <& box (theTok RPAR))
      app    = (λ where (p , c) e → p > e `$ c) <$>
                (getPosition <M&> ((uncurry _>`-_ <$> (getPosition <M&> var))
                              <|> parens □check))
      infer  = iterate (var <|> cut <|> parens (INS.map commit □infer))
                       (box app)
      lam    = (λ where ((p , x) , c) → p >`λ x ↦ c)
               <$> (theTok LAM &> box (getPosition <M&> name)
               <&> box (theTok DOT &> INS.map commit □check))
      letin  = (λ where (((p , x) , e) , c) → p >`let x ↦ e `in c)
               <$> (theTok LET &> box (getPosition <M&> name)
               <&> box (theTok EQ &> INS.map commit □infer)
               <&> box (theTok IN &> INS.map commit □check)
               )
      emb    = uncurry _>`-_ <$> (getPosition <M&> infer)
      check  = lam <|> letin <|> emb
  in record { infer = infer <|> parens (INS.map commit □infer)
            ; check = check <|> parens (INS.map commit □check)
            }

parse : String → Types.Result (Parsed Infer)
parse str = result inj₁ inj₁ (inj₂ ∘′ Success.value ∘′ proj₁)
   $′ runParser (infer bidirectional) ≤-refl input (start , [])
   where
     input = Vec.fromList $ tokenize str
     module M = RawMonad ParserM.monad

open import Agda.Builtin.Equality

_ : tokenize "(λ x . 1 : `a → `a)"
    ≡ (0 ∶ 0  , LPAR)
    ∷ (0 ∶ 1  , LAM)
    ∷ (0 ∶ 3  , ID "x")
    ∷ (0 ∶ 5  , DOT)
    ∷ (0 ∶ 7  , ID "1")
    ∷ (0 ∶ 9  , COL)
    ∷ (0 ∶ 11 , ID "`a")
    ∷ (0 ∶ 14 , ARR)
    ∷ (0 ∶ 16 , ID "`a")
    ∷ (0 ∶ 18 , RPAR)
    ∷ []
_ = refl

_ : parse "(λ x . 1 : `a → `a)" ≡ inj₁ At 0 ∶ 7 ParseError
_ = refl

_ : tokenize "(λ x . x : `a → `a)"
    ≡ (start , LPAR)
    ∷ (0 ∶ 1 , LAM)
    ∷ (0 ∶ 3 , ID "x")
    ∷ (0 ∶ 5 , DOT)
    ∷ (0 ∶ 7 , ID "x")
    ∷ (0 ∶ 9 , COL)
    ∷ (0 ∶ 11 , ID "`a")
    ∷ (0 ∶ 14 , ARR)
    ∷ (0 ∶ 16 , ID "`a")
    ∷ (0 ∶ 18 , RPAR)
    ∷ []
_ = refl

_ : parse "(λ x . x : `a → `a)"
    ≡ inj₂ (_ > _ >`λ "x" ↦ (_ >`- `var _  "x") `∶ (α "a" ⇒ α "a"))
_ = refl

_ : parse "(let x = (λf.f : `a → `a) in x : `a → `a)"
    ≡ inj₂ (_ >
      _ >`let "x" ↦ _ > _ >`λ "f" ↦ (_ >`- (`var _ "f"))
                     `∶ (α "a" ⇒ α "a")
         `in (_ >`- `var _ "x") `∶ (α "a" ⇒ α "a"))
_ = refl
