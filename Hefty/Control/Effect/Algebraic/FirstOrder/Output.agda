module Control.Effect.Algebraic.FirstOrder.Output
    where

open import Foundation.Base

open import Control.Effect.Algebraic.Effect
open import Control.Effect.Algebraic.Effect.Free

open import Agda.Builtin.String
open import Agda.Builtin.Unit

data OutOp : Set1 where
    out : String -> OutOp

Output : Effect
Op  Output = OutOp
Ret Output (out str) = ⊤

