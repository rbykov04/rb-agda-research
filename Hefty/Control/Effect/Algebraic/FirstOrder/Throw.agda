module Control.Effect.Algebraic.FirstOrder.Throw
    where

open import Foundation.Base
open import Control.Effect.Algebraic.Effect

data ThrowOp : Set where
    throw : ThrowOp

Throw : Effect
Op Throw = ThrowOp
Ret Throw throw = ⊥

data ThrowErrorOp (S : Set) : Set1 where
    throwE : S -> ThrowErrorOp S

ThrowError : (S : Set) -> Effect
ThrowError S = record
    { Op = ThrowErrorOp S
    ; Ret = λ where
        (throwE _) → ⊥
    }
