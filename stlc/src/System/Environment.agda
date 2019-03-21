module System.Environment where

open import Data.List.Base using (List)
open import Data.String.Base using (String)

import IO.Primitive as Prim
open import IO

private
  postulate
    primGetArgs : Prim.IO (List String)

{-# FOREIGN GHC import qualified System.Environment as Env     #-}
{-# FOREIGN GHC import qualified Data.Text as T                #-}
{-# COMPILE GHC primGetArgs = fmap (fmap T.pack) Env.getArgs #-}

getArgs : IO (List String)
getArgs = lift primGetArgs
