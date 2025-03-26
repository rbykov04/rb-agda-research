module Control.Effect.Algebraic.FirstOrder.Teletype
    where

open import Agda.Builtin.Unit
open import Agda.Builtin.Char

open import Foundation.Base

open import Control.Effect.Algebraic.Effect

data TeletypeOp : Set1 where
  putChar  : Char   -> TeletypeOp
  getChar  : TeletypeOp

Teletype : Effect
Teletype .Op              = TeletypeOp
Teletype .Ret (putChar x) = ⊤
Teletype .Ret getChar     = Char
