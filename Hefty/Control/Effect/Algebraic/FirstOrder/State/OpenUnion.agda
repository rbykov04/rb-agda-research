module Control.Effect.Algebraic.FirstOrder.State.OpenUnion
    where

open import Agda.Builtin.String
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

runState
  : {s a : Level} {S : Type s} {Effs : Effect s s} {A : Type a}
  → Free (State S ⊕ Effs) A
  → S
  → Free Effs (S × A)
runState =
  fold
    (λ a s → pure (s , a) )
    (λ where
      (inl (modify f)) k s → k (f s) (f s)
      (inr op) k s → impure op λ ret → k ret s
    )
