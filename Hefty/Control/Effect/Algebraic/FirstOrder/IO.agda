module Control.Effect.Algebraic.FirstOrder.IO
    where

open import Agda.Builtin.IO public

open import Foundation.Base

open import Control.Effect.Algebraic.Effect
open import Control.Effect.Algebraic.Effect.Free hiding ( _>>=_ ; _>>_ )


private
  variable
    a b : Level
    A : Set a
    B : Set b

postulate
    return : A → IO A
    _>>=_  : IO A → (A → IO B) → IO B
{-# COMPILE GHC return = \_ _ -> return    #-}
{-# COMPILE GHC _>>=_  = \_ _ _ _ -> (>>=) #-}

infixl 1 _>>_
_>>_ : IO A → IO B → IO B
a >> b = a >>= λ _ → b


data IOOP : Set1 where
  liftIO  : (A : Set) -> IO A ->  IOOP


IOEF : Effect
IOEF .Op = IOOP
IOEF .Ret (liftIO ty x) = ty

execAlgebra : Alg IOEF (IO A)
execAlgebra (liftIO ty f) k = f >>= k

exec : Free IOEF A -> IO A
exec = fold return execAlgebra

