module Control.Effect.Algebraic.FirstOrder.State
    where

open import Agda.Builtin.Unit
open import Agda.Builtin.String
open import Agda.Builtin.Char

open import Agda.Builtin.Equality
open import Foundation.Base

open import Control.Effect.Algebraic.Effect

data StateOp (S : Set) : Set1  where
    get : StateOp S
    put : S -> StateOp S


State : (S : Set) -> Effect
State S = record
    { Op = StateOp S
    ; Ret = λ where
        get  → S
        (put _) → ⊤
    }

