module Mystdlib.IO where

open import Agda.Builtin.String
open import Agda.Builtin.IO
open import Agda.Builtin.Unit

open import Agda.Primitive
private
  variable
    a b c d e : Level
    A : Set a
    B : Set b
    C : Set c
    D : Set d
    E : Set e


infixl 1 _>>>=_
postulate
    putStr : String → IO ⊤
    return : A → IO A
    _>>>=_  : IO A → (A → IO B) → IO B


{-# FOREIGN GHC import qualified Data.Text as T #-}
{-# FOREIGN GHC import qualified System.IO as SIO #-}
{-# COMPILE GHC putStr = (SIO.hPutStr SIO.stderr) . T.unpack #-}
{-# COMPILE GHC return = \_ _ -> return    #-}
{-# COMPILE GHC _>>>=_  = \_ _ _ _ -> (>>=) #-}

_>>>_ : IO A → IO B → IO B
a >>> b = a >>>= λ _ → b
