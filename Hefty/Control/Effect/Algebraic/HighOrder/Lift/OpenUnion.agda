module Control.Effect.Algebraic.HighOrder.Lift.OpenUnion
    where

open import Foundation.Base

open import Control.Effect.Algebraic.Effect
open import Control.Effect.Algebraic.FirstOrder.Nil
open import Control.Effect.Algebraic.HighOrder.Lift
open import Control.Effect.Algebraic.Hefty
open import Control.Effect.Algebraic.Effect.Free
open import Control.Effect.Algebraic.Hefty.RowInsert hiding (inject)
open import Control.Effect.Algebraic.Effect.OpenUnion
open import Control.Effect.Algebraic.Effect.OpenUnion.Properties


eLift :
        {E Effs : FirstEffect }
        {{w : E ∈ Effs}}
        -> Elaboration (Lift E) Effs
eLift ⦃ w ⦄ .alg op fork k = impure (inject w op) λ ret → k (project w ret)

instance
  eLift′
    :  {E Effs : FirstEffect}
    -> {{w : E ∈ Effs}}
    -> Elab (Lift E) Effs
  orate eLift′ = eLift
