module Control.Effect.Algebraic.HighOrder.Lift.RowInsert
    where

open import Foundation.Base

open import Control.Effect.Algebraic.Effect
open import Control.Effect.Algebraic.FirstOrder.Nil
open import Control.Effect.Algebraic.HighOrder.Lift
open import Control.Effect.Algebraic.Hefty
open import Control.Effect.Algebraic.Effect.Free
open import Control.Effect.Algebraic.Hefty.RowInsert hiding (inject)
open import Control.Effect.Algebraic.Effect.RowInsert


eLift :
        {E E1 Effs : FirstEffect }
        {{w : effrow Effs ＝ E ∣ E1 }}
        -> Elaboration (Lift E) Effs
eLift ⦃ w ⦄ .alg op fork k =
  impure (inj-insert-left2 {{ w }} op) λ ret → k (proj-ret-left2 {{w}} ret)
{-
instance
  eLift′
    :  {E Effs : FirstEffect}
    -> {{w : E ∈ Effs}}
    -> Elab (Lift E) Effs
  orate eLift′ = eLift
-}
