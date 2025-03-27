{-# OPTIONS  --backtracking-instance-search  #-}
module Example.Reproduce where

open import Agda.Builtin.Unit
open import Agda.Builtin.Char
open import Agda.Builtin.IO

data IOOP : Set1 where
  liftIO  : (A : Set) -> IO A ->  IOOP

postulate
    putChar : Char → IO ⊤

{-# FOREIGN GHC import qualified Data.Text as T #-}
{-# FOREIGN GHC import qualified System.IO as SIO #-}
{-# COMPILE GHC putChar = (SIO.hPutChar SIO.stderr) #-}


main : IO ⊤
main = putChar 'a'
