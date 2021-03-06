module Print where

open import Data.Bool using (true; false; if_then_else_; _∧_)
open import Data.Nat as Nat
import Data.Nat.Show as NShow
open import Data.String
open import Data.Char
open import Data.Char.Unsafe
open import Data.Product
open import Data.Maybe
open import Data.List.Base as List using ([])
open import Function

open import var
open import environment
import Generic.Semantics.Printing as Printing

open import Language
open Internal

import Data.Map as M
private
  module Map = M.Map Nat._≟_ String
open Map using (Map)

type : Type ℕ → Map → String
type (α k)         mp = maybe ("`" ++_) (NShow.show k) (Map.assoc k mp)
type (σ@(α _) ⇒ τ) mp = type σ mp ++ " → " ++ type τ mp
type (σ       ⇒ τ) mp = "(" ++ type σ mp ++ ") → " ++ type τ mp
type (σ@(α _) ⊗ τ) mp = type σ mp ++ " * " ++ type τ mp
type (σ       ⊗ τ) mp = "(" ++ type σ mp ++ ") * " ++ type τ mp

print : ∀ {P mσ} → Internal P mσ [] → Map → String
print t mp = Printing.print display t where

  display = Printing.mkD $ λ where
    (p , t `∶' σ)             → "(" ++ t ++ " : " ++ type σ mp ++ ")"
    (p , f `$' t)             → f ++ " " ++ parens? t
    (p , `fst' e)             → "fst " ++ parens? e
    (p , `snd' e)             → "snd " ++ parens? e
    (p , `λ' (x , b))         → "λ" ++ lookup x z ++ "." ++ b
    (p , a `,' b)             → "(" ++ a ++ ", " ++ b ++ ")"
    (p , `let' e `in (x , b)) → "let " ++ lookup x z ++ " = " ++ e ++ " in " ++ b
    (p , `-' t)               → t


      where parens? : String → String
            parens? t = let cs = toList t in
              if maybe′ ('(' ==_) true (List.head cs)
               ∧ maybe′ (')' ==_) true (List.head (List.reverse cs)) then t
              else if List.any isSpace cs then "(" ++ t ++ ")" else t
