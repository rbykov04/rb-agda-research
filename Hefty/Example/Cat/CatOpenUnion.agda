module Example.Cat.CatOpenUnion where

open import Agda.Builtin.Unit
open import Agda.Builtin.String

open import Foundation.Base
open import Control.Effect.Algebraic.Effect
open import Control.Effect.Algebraic.Effect.Free
open import Control.Effect.Algebraic.Effect.OpenUnion
open import Control.Effect.Algebraic.Effect.OpenUnion.Properties

open import Control.Effect.Algebraic.FirstOrder.IO hiding (_>>_ ; _>>=_)
open import Control.Effect.Algebraic.FirstOrder.Filesystem
open import Control.Effect.Algebraic.FirstOrder.Filesystem.OpenUnion
open import Control.Effect.Algebraic.FirstOrder.Teletype
open import Control.Effect.Algebraic.FirstOrder.Teletype.OpenUnion

cat
  : {Effs : Effect {lsuc lzero} {lzero}}
  -> {{ Teletype   ∈ Effs }}
  -> {{ Filesystem ∈ Effs }}
  -> String
  -> Free Effs ⊤
cat file = do
  txt <- send $ readFile file
  putStrLn txt



program : Free (Filesystem ⊕ Teletype ⊕ IOEF) ⊤
program = do
  cat "test.txt"


program2 : Free (Teletype ⊕ Filesystem ⊕ IOEF) ⊤
program2 = do
  cat "test.txt"

main : IO ⊤
main = exec (givenHandle hTeletype
            (givenHandle hFilesystem program tt) tt)

main1 : IO ⊤
main1 = exec (givenHandle hFilesystem
             (givenHandle hTeletype program2 tt) tt)

