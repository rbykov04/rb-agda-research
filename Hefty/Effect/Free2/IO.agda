module Effect.Free2.IO where

open import Agda.Builtin.Unit
open import Agda.Builtin.Sigma
open import Agda.Builtin.List
open import Agda.Builtin.Char
open import Agda.Builtin.String
open import Agda.Builtin.IO
open import Agda.Builtin.Equality
open import Agda.Primitive

open import Mystdlib.Mystdlib

open import Effect.Core.Free2 hiding ( _>>=_ ; _>>_ )

private
  variable
    a b c d e : Level
    A : Set a
    B : Set b
    C : Set c
    D : Set d
    E : Set e

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


IOEF : Effect2
IOEF .Op = IOOP
IOEF .Ret (liftIO ty x) = ty

execAlgebra2 : Alg2 IOEF (IO A)
execAlgebra2 (liftIO ty f) k = f >>= k

exec2 : Free2 IOEF A -> IO A
exec2 = fold2 return execAlgebra2
