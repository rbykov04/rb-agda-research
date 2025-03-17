{-# OPTIONS  --backtracking-instance-search  #-}
module Example.Resource where

open import Agda.Builtin.Unit
open import Agda.Builtin.Sigma
open import Agda.Builtin.List
open import Agda.Builtin.Char
open import Agda.Builtin.String
open import Agda.Builtin.IO
open import Agda.Builtin.Equality
open import Agda.Primitive

open import Mystdlib.Mystdlib

open import Effect.Core.Free hiding ( _>>=_ ; _>>_ )
open import Effect.Core.Free2
open import Effect.Free2.IO hiding (return; _>>_; _>>=_)
open import Effect.Free2.State
open import Effect.Free2.Teletype
open import Effect.Free2.Filesystem

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
    _>>>=_  : IO A → (A → IO B) → IO B
{-# FOREIGN GHC import qualified Data.Text as T #-}
{-# FOREIGN GHC import qualified System.IO as SIO #-}
{-# COMPILE GHC return = \_ _ -> return    #-}
{-# COMPILE GHC _>>>=_  = \_ _ _ _ -> (>>=) #-}

infixl 1 _>>>_
_>>>_ : IO A → IO B → IO B
a >>> b = a >>>= λ _ → b


cat : {E There1 There2 : Effect2}
      -> {{ EffectStorage2 E Teletype   There1 }}
      -> {{ EffectStorage2 E Filesystem There2 }}
      -> String
      -> Free2 E ⊤
cat file = do
  file <- readFile file
  putStrLn file

program : Free2 (Filesystem |2> Teletype |2> IOEF) ⊤
program = do
  cat "test.txt"

main : IO ⊤
main = exec2 (givenHandle2 hTeletype
            (givenHandle2 hFilesystem program tt) tt) >>>= \ x -> return tt
