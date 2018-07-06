module Print where

open import Data.Nat as Nat
import Data.Nat.Show as NShow
open import Data.String
open import Data.Product
open import Data.Maybe
open import Data.List using ([])
open import Function

open import var
open import environment
open import Generic.Syntax
import Generic.Semantics.Printing as Printing

open import Language
open Internal

import Data.Map as M
module Map = M.Map Nat._≟_ String
open Map using (Map)

type : Type ℕ → Map → String
type (α k)         mp = maybe ("`" ++_) (NShow.show k) (Map.assoc k mp)
type (σ@(α _) ⇒ τ) mp = type σ mp ++ " → " ++ type τ mp
type (σ       ⇒ τ) mp = "(" ++ type σ mp ++ ") → " ++ type τ mp

print : ∀ {mσ} → Typed mσ [] → Map → String
print t mp = Printing.print display t where

  display = Printing.mkD $ λ where
    (p , t `∶' σ)      → "(" ++ t ++ " : " ++ type σ mp ++ ")"
    (p , f `$' t)      → f ++ " " ++ t
    (p , `λ' (x , b))  → "λ" ++ lookup x z ++ "." ++ b
    (p , `-' t)        → t