module Experimental.17-IO
    where

open import Agda.Builtin.IO
open import Agda.Builtin.Unit
open import Agda.Builtin.Nat
open import Agda.Builtin.Bool
open import Agda.Builtin.Sigma
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
IOEF A .Ret x = A


execAlgebra : Alg (IOEF A) (IO B)
execAlgebra op k = op >>=IO k

exec : Free (IOEF A) A → IO A
exec = Control.Effect.Algebraic.Effect.Free.fold return execAlgebra

exec1 : Free (IOEF A) (IO A) → IO A
exec1 = Control.Effect.Algebraic.Effect.Free.fold id execAlgebra

runIO : Free ( IOEF A ⊕ IOEF B ) B → IO B
runIO = Control.Effect.Algebraic.Effect.Free.fold return func
  where
  func : _
  func (inl op) k = op >>=IO k
  func (inr op) k = op >>=IO k



program : {Effs : Effect {lzero} {lzero} }
      → {{IOEF ⊤ ∈ Effs }}
      → Free Effs ⊤
program = do
  send (putCharIO 'h')
  send (putCharIO 'e')
  send (putCharIO 'l')
  send (putCharIO 'l')
  send (putCharIO 'o')
  send (putCharIO '\n')


program1 : {Effs : Effect {lzero} {lzero} }
          → {{IOEF Char ∈ Effs }}
          → {{IOEF ⊤ ∈ Effs }}
          → Free Effs ⊤
program1 = do
  send (putCharIO 'h')
  send (putCharIO 'e')
  send (putCharIO 'l')
  send (putCharIO 'l')
  send (putCharIO 'o')
  send (putCharIO '\n')
  a <- send (getCharIO)
  send (putCharIO a)
  send (putCharIO a)
  send (putCharIO a)
  send (putCharIO a)

main1 : IO ⊤
main1 = (runIO program1)
