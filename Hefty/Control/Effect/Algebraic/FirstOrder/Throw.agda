module Control.Effect.Algebraic.FirstOrder.Throw
    where

open import Foundation.Base
open import Control.Effect.Algebraic.Effect

data ThrowOp : Set where
    throw : ThrowOp

Throw : Effect
Op Throw = ThrowOp
Ret Throw throw = ⊥

