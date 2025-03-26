module Control.Effect.Algebraic.FirstOrder.State
    where

open import Agda.Builtin.Unit
open import Agda.Builtin.String
open import Agda.Builtin.Char

open import Foundation.Base

open import Control.Effect.Algebraic.Effect

data StatePolyOp {s : Level} (S : Set s) : Set s  where
    get : StatePolyOp S
    put : S -> StatePolyOp S


StatePoly : {s : Level} (T : Set s) (S : Set s) -> Effect {s} {s}
StatePoly T S = record
    { Op = StatePolyOp S
    ; Ret = λ where
        get  → S
        (put _) →  T
    }


State' : (S : Set) ->  Effect
State' S = StatePoly ⊤ S

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

