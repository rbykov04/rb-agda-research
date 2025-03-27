module Experimental.7-PolyState
    where

open import Agda.Builtin.Unit
open import Agda.Builtin.String
open import Agda.Builtin.Char

open import Agda.Builtin.Equality
open import Foundation.Base

open import Control.Effect.Algebraic.Effect

data One (a : Level) : Set a where
    one : One a

to : One lzero -> ⊤
to = λ _ → tt

from : ⊤ -> One lzero
from = λ _ → one

proof1 : (x : ⊤) -> to (from x) ≡ x
proof1 = λ x → refl

proof2 : (x : One lzero) -> from (to x) ≡ x
proof2 one = refl

{-
proof3 : ⊤ ≡ One lzero
proof3 = {!!}
-}


data StatePolyOp {s : Level} (S : Set s) : Set s  where
    get : StatePolyOp S
    put : S -> StatePolyOp S



StatePoly : {s : Level} (S : Set s) -> Effect {s} {s}
StatePoly {s} S = record
    { Op = StatePolyOp S
    ; Ret = λ where
        get  → S
        (put _) →  One s
    }

State' : (S : Set) ->  Effect
State' S = StatePoly S


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

