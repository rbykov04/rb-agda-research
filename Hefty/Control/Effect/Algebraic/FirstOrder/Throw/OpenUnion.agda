module Control.Effect.Algebraic.FirstOrder.Throw.OpenUnion
    where

open import Agda.Builtin.Maybe
open import Agda.Builtin.Unit

open import Foundation.Base

open import Control.Effect.Algebraic.Effect
open import Control.Effect.Algebraic.Effect.OpenUnion
open import Control.Effect.Algebraic.Effect.OpenUnion.Properties
open import Control.Effect.Algebraic.Effect.Free
open import Control.Effect.Algebraic.FirstOrder.Throw

private
  variable
    a b c d e : Level
    A : Set a
    B : Set b
    C : Set c
    D : Set d
    E : Set e



hThrow :  {Effs : Effect} -> Handler A Throw ⊤ (Maybe A) Effs
ret hThrow x _ = pure (just x)
hdl hThrow throw _ _ = pure nothing
