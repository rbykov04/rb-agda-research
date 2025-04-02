module Control.Effect.Algebraic.FirstOrder.Output.OpenUnion
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
open import Control.Effect.Algebraic.FirstOrder.Output

private
  variable
    a b c d e : Level
    A : Set a
    B : Set b
    C : Set c
    D : Set d
    E : Set e


hOut : {Effs : Effect} -> Handler A Output ⊤ (String × A ) Effs
ret hOut x _ = pure ("" , x)
hdl hOut (out s) k p = do (s', x) <- k tt p; pure (s ++ s' , x)
