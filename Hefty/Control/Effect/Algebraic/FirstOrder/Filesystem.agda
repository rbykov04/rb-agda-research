module Control.Effect.Algebraic.FirstOrder.Filesystem
    where

open import Agda.Builtin.Unit
open import Agda.Builtin.String
open import Agda.Builtin.Char

open import Foundation.Base

open import Control.Effect.Algebraic.Effect

data FileSystemOp : Set1 where
  readFile   : String -> FileSystemOp
  writeFile  : String -> String -> FileSystemOp

Filesystem : Effect
Filesystem .Op                        = FileSystemOp
Filesystem .Ret (readFile file)       = String
Filesystem .Ret (writeFile file text) = ⊤
