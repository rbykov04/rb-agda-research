module Control.Effect.Algebraic.FirstOrder.State.OpenUnion
    where

open import Agda.Builtin.String
open import Agda.Builtin.Sigma
open import Agda.Builtin.Char
open import Agda.Builtin.List
open import Agda.Builtin.Unit
open import Agda.Builtin.IO

open import Foundation.Base

open import Control.Effect.Algebraic.Effect
open import Control.Effect.Algebraic.Effect.OpenUnion
open import Control.Effect.Algebraic.Effect.OpenUnion.Properties
open import Control.Effect.Algebraic.Effect.Free
open import Control.Effect.Algebraic.FirstOrder.State

private
  variable
    a b c d e : Level
    A : Set a
    B : Set b
    C : Set c
    D : Set d
    E : Set e


hState : {Eff : Effect} {S : Set}
    -> Handler A (State S) S ( S × A ) Eff
ret hState x s = pure (s , x)
hdl hState get k n = k n n
hdl hState (put m) k _ = k tt m

runState
  : {A S : Set} {Effs : Effect {lsuc lzero} {lzero}}
  → Free (State S ⊕ Effs) A
  → S
  → Free Effs (S × A)
runState prog init = do
  (s , a ) <- givenHandle hState prog init
  pure ((s , a))
