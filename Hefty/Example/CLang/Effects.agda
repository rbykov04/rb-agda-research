module Example.CLang.Effects
    where

open import Agda.Builtin.Char
open import Agda.Builtin.Unit
open import Agda.Builtin.String
open import Agda.Builtin.Bool
open import Agda.Builtin.Nat
open import Agda.Builtin.List
open import Agda.Builtin.Maybe
open import Agda.Builtin.Sigma
open import Agda.Builtin.Equality

open import Foundation.Base
open import Data.String.Base
open import Data.Vec.Base

open import Control.Effect.Algebraic.FirstOrder.Nil
open import Control.Effect.Algebraic.FirstOrder.State
open import Control.Effect.Algebraic.FirstOrder.Throw
open import Control.Effect.Algebraic.Effect
open import Control.Effect.Algebraic.Effect.Free hiding (_>>_ ; _>>=_)
open import Control.Effect.Algebraic.Effect.RowInsert
open import Control.Effect.Algebraic.Hefty hiding (_>>_ ; _>>=_)
open import Control.Effect.Algebraic.HighOrder.Lift
open import Control.Effect.Algebraic.HighOrder.Lift.OpenUnion
open import Control.Effect.Algebraic.Hefty.RowInsert
open import Example.CLang.TokenTypes

private
  variable
    a b c d e : Level
    A : Set a
    B : Set b
    C : Set c
    D : Set d
    E : Set e


data TokenizerOp : Set1
    where
    addToken : Token → TokenizerOp

TokenizerResult : FirstEffect
TokenizerResult = record
    { Op = TokenizerOp
    ; Ret = λ where
        (addToken _)  → ⊤
    }

data LoggerOp : Set1
    where
    log : String → LoggerOp


Logger : FirstEffect
Logger = record
    { Op = LoggerOp
    ; Ret = λ where
        (log _)  → ⊤
    }


TokenThrow = ThrowError (Nat × String)


throwError : {Effs E : Effect} { A : Set  }
    → ⦃ effrow Effs ＝ TokenThrow ∣ E ⦄
    → Nat
    → String
    → Free Effs A
throwError pos text  = do
        x <- send (throwE (pos , text))
        ⊥-elim x
    where open import Control.Effect.Algebraic.Effect.Free using (_>>=_ ; _>>_)

throwErrorᴴ : {H H' : Effectᴴ} { A : Set  }
    → ⦃ heftyrow H ＝ (Lift TokenThrow) ∣ H' ⦄
    → Nat
    → String
    → Hefty H A
throwErrorᴴ pos text  = do
        x <- up (throwE (pos , text))
        ⊥-elim x
    where open import Control.Effect.Algebraic.Hefty using (_>>=_ ; _>>_)


hResult : {Effs : Effect} -> Handler A TokenizerResult ⊤ (List Token × A ) Effs
hResult .ret x _ = pure ([] , x)
hResult .hdl (addToken tok) k p = do
    (s' , x) <- k tt p
    pure ((tok ∷ s') , x)
    where
        open import Control.Effect.Algebraic.Effect.Free using (_>>=_ ; _>>_)

hLogger : {Effs : Effect} -> Handler A Logger ⊤ (String × A ) Effs
hLogger .ret x _ = pure ("" ,  x)
hLogger .hdl (log str) k p = do
    (s' , x) <- k tt p
    pure ((str ++ "\n" ++ s') , x)
    where
        open import Control.Effect.Algebraic.Effect.Free using (_>>=_ ; _>>_)


hThrow : {Effs : Effect} -> Handler A TokenThrow ⊤ (Maybe A) Effs
hThrow .ret x _ = pure (just x)
hThrow .hdl (throwE code) k x = pure nothing


