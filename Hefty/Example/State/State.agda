
module Example.State.State where

open import Agda.Builtin.Unit
open import Agda.Builtin.String

open import Mystdlib.Universe
open import Foundation.Base

open import Control.Effect.Algebraic.Effect
open import Control.Effect.Algebraic.Effect.Free
open import Control.Effect.Algebraic.Effect.OpenUnion
open import Control.Effect.Algebraic.Effect.OpenUnion.Properties

open import Control.Effect.Algebraic.FirstOrder.IO hiding (_>>_ ; _>>=_)
open import Control.Effect.Algebraic.FirstOrder.Filesystem
open import Control.Effect.Algebraic.FirstOrder.Filesystem.OpenUnion
open import Control.Effect.Algebraic.FirstOrder.Teletype
open import Control.Effect.Algebraic.FirstOrder.State

data StateType : Set where
  unit  : StateType
  state   : StateType


data StateOp  {{u : Universe}} : Set  where
    get : Ty -> StateOp
    put :  Ty -> Ty -> StateOp

State : {{u : Universe}} -> Effect
State = record
    { Op = StateOp
    ; Ret = λ where
        (get t) → [[ t ]]
        (put t x) →  [[ t ]]
    }

instance
  TypeUniverse : Universe
  Ty  ⦃ TypeUniverse ⦄ = StateType
  [[_]] ⦃ TypeUniverse ⦄ unit = ⊤
  [[_]] ⦃ TypeUniverse ⦄ state  = String

program
  : {Effs : Effect }
  -> {{ State ∈ Effs }}
  -> {{u : Universe}}
  -> Free Effs ⊤
program = do
    send (put state {!!})
