{-# OPTIONS  --backtracking-instance-search  #-}
module Effect.Nil where

open import Agda.Builtin.String
open import Agda.Builtin.Unit
open import Agda.Builtin.Maybe
open import Agda.Builtin.Bool
open import Agda.Builtin.List
open import Agda.Builtin.Nat
open import Agda.Builtin.Equality
open import Agda.Builtin.IO
open import Agda.Builtin.Unit
open import Agda.Builtin.String
open import Agda.Builtin.Sigma
open import Agda.Primitive

open import Mystdlib.Mystdlib
open import Mystdlib.IO

open import Effect.Core.Free hiding (_>>=_; _>>_)
open import Effect.Core.Hefty
open import Effect.Free.State
open import Effect.Free.Output
open import Effect.Free.Throw
open import Effect.Free.Nil
open import Effect.Hefty.Catch
open import Effect.Hefty.Lift

private
  variable
    a b c d e : Level
    A : Set a
    B : Set b
    C : Set c
    D : Set d
    E : Set e

eNil : {Eff : Effect} -> Elaboration (Lift Nil) Eff
alg eNil ()

instance
  eNil′ : {Eff : Effect} -> Elab (Lift Nil) Eff
  orate eNil′ = eNil
