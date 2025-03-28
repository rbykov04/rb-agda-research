module Example.Censor.Censor where

open import Agda.Builtin.Unit
open import Agda.Builtin.String

open import Foundation.Base
open import Control.Effect.Algebraic.Hefty


data CensorOp : Set where
    censor : (String -> String) -> CensorOp

Censor : Effectᴴ
Censor = record
    { Opᴴ = CensorOp
    ; Fork  = λ where
        (censor str) -> record
            { Op = ⊤
            ; Ret = λ _ → ⊤
            }
    ; Retᴴ = λ where
       (censor str) → ⊤
    }

{-
-- what is it?
censorOP : {H : EffectH} -> (String -> String) -> Hefty (Censor +E+ H) ⊤ -> Hefty (Censor +E+ H) ⊤
censorOP f m = impure (injl (censor f)) (\ _ → m) pure

censor1 : {H : EffectH} -> Hefty Censor Nat
censor1  = impure (censor (\ s → s ++ ".")) pure \ _ → pure zero
-}
