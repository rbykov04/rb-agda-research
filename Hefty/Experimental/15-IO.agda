module Experimental.15-IO
    where

open import Agda.Builtin.IO
open import Agda.Builtin.Unit
open import Agda.Builtin.Nat
open import Agda.Builtin.Bool
open import Agda.Builtin.String
open import Agda.Builtin.Char
open import Agda.Builtin.List
open import Agda.Primitive
open import Agda.Builtin.Equality
open import Foundation.Base

open import Control.Effect.Algebraic.Effect
open import Control.Effect.Algebraic.Hefty hiding (_>>=_; _>>_)
open import Control.Effect.Algebraic.Effect.Free
--open import Control.Effect.Algebraic.Effect.RowInsert
open import Control.Effect.Algebraic.Effect.OpenUnion
open import Control.Effect.Algebraic.Effect.OpenUnion.Properties


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
    _>>=IO_  : IO A → (A → IO B) → IO B
    putCharIO : Char -> IO ⊤
    getCharIO : IO Char
    readFileIO  : String -> IO String
    writeFileIO : String -> String -> IO ⊤
{-# FOREIGN GHC import qualified Data.Text as T #-}
{-# COMPILE GHC writeFileIO = \ path text -> writeFile (T.unpack path) (T.unpack text) #-}
{-# COMPILE GHC readFileIO = \ path ->  readFile (T.unpack path) >>= \ text -> return (T.pack text) #-}
{-# FOREIGN GHC import qualified Data.Text as T #-}
{-# FOREIGN GHC import qualified System.IO as SIO #-}
{-# COMPILE GHC putCharIO = (SIO.hPutChar SIO.stderr) #-}
{-# COMPILE GHC getCharIO = SIO.getChar #-}
{-# COMPILE GHC _>>=IO_  = \_ _ _ _ -> (>>=) #-}


IOEF : (A : Set) → Effect {lzero} {lzero}
IOEF A .Op = IO A
IOEF A .Ret x = IO A


hIO : {Eff : Effect {lzero} {lzero}}
    → ( B : Set )
    → Handler (IO A) (IOEF B) A (IO A) Eff
hIO A .ret x _ = pure x
hIO A .hdl op k x = k op x



putStrLn1 : {Effs : Effect {lzero} {lzero} }
      → {{IOEF ⊤ ∈ Effs }}
      → String
      → Free Effs (IO ⊤)
putStrLn1 str = pure (f (primStringToList str)) where
  f : List Char → IO ⊤
  f [] = putCharIO '\n'
  f (x ∷ str) = putCharIO x >>=IO λ _ → f str



putStrLn : {Effs : Effect {lzero} {lzero} }
      → {{IOEF ⊤ ∈ Effs }}
      → IO String
      → Free Effs (IO ⊤)
putStrLn x = pure (x >>=IO λ str → f (primStringToList str)) where
  f : List Char → IO ⊤
  f [] = putCharIO '\n'
  f (x ∷ str) = putCharIO x >>=IO λ _ → f str

cat : {Effs : Effect {lzero} {lzero} }
      → {{IOEF String ∈ Effs }}
      → {{IOEF ⊤ ∈ Effs }}
      → Free Effs (IO ⊤)
cat = do
  str <- send (readFileIO "test.txt")
  putStrLn str


Nil : Effect {lzero} {lzero}
Op  Nil = ⊥
Ret Nil = λ ()


un : Free Nil A -> A
un (pure x) = x

main : IO ⊤
main = un (givenHandle (hIO ⊤) (givenHandle (hIO String ) cat tt) tt)
