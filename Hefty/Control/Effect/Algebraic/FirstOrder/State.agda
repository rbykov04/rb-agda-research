module Control.Effect.Algebraic.FirstOrder.State
    where

open import Agda.Builtin.Unit
open import Agda.Builtin.String
open import Agda.Builtin.Char

open import Foundation.Base

open import Control.Effect.Algebraic.Effect

open import Mystdlib.Universe
{-
data StateType : Set where
  unit  : StateType
  state   : StateType


data StateOp {s : Level} ( S : Set s ) {{u : Universe}} : Set s  where
    get : StateOp S
    put : Ty -> S -> StateOp S

State : {s : Level} ( S : Set s ) {{u : Universe}} -> Effect
State S = record
    { Op = StateOp S
    ; Ret = λ where
        (get ) → S
        (put t _) → [[ t ]]
    }
-}
{-
instance
  TypeUniverse : Universe
  Ty  ⦃ TypeUniverse ⦄ = StateType
  [[_]] ⦃ TypeUniverse ⦄ unit = ⊤
  [[_]] ⦃ TypeUniverse ⦄ num  = {!!}
-}
