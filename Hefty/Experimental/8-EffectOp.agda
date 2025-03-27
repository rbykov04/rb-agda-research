module Experimental.8-EffectOp
    where

open import Agda.Builtin.Unit
open import Agda.Builtin.String
open import Agda.Builtin.Char

open import Agda.Builtin.Equality
open import Foundation.Base

open import Control.Effect.Algebraic.Effect


EffectOp = Set1

data StateOp (S : Set) : EffectOp  where
    get : StateOp S
    put : S -> StateOp S


State : (S : Set) -> Effect
State S = record
    { Op = StateOp S
    ; Ret = λ where
        get  → S
        (put _) → ⊤
    }

