module Control.Effect.Algebraic.HighOrder.Lift
    where

open import Foundation.Base

open import Control.Effect.Algebraic.Effect
open import Control.Effect.Algebraic.FirstOrder.Nil
open import Control.Effect.Algebraic.Hefty
open import Control.Effect.Algebraic.Hefty.RowInsert

private
  variable
    a o k r : Level
    A : Set a
    E : Effect {k} {r}
    H H0 H' H'' Row Compl : Effectᴴ {o} {k} {r}
    X Y Z Y\X : Effectᴴ {o} {o ⊔ r} {r}


Lift : FirstEffect -> HighEffect
Opᴴ   (Lift x)   = Op x
Fork (Lift x) _  = Nil
Retᴴ  (Lift x)   = Ret x

up
    : {{ w : heftyrow H ＝ (Lift E) ∣ H' }}
    -> (op : Op E)
    -> Hefty H (Ret E op)
up {{w}} op = impure (inject {{w}} op)
                     (proj-fork-l {{w}} op (λ ()))
                     \ x → pure (project-ret {{w}} x)
{-
FIXME
eLift : {Eff Eff0 Eff' : Effect}
        {{w : EffectStorage Eff Eff0 Eff'}}
        -> Elaboration (Lift Eff0) Eff
alg (eLift ⦃ w = w ⦄) op fork k = impure (inj-insert-left op)
                                  \ ret → k (proj-ret-left {{w}} ret)
instance
  eLift′
    :  {Row E Compl : Effect}
    -> ⦃ effrow Row ＝ E ∣ Compl ⦄
    -> Elab (Lift E) Row
  orate eLift′ = eLift

-}
