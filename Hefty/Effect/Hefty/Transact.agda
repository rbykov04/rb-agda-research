
{-# OPTIONS --exact-split #-}
{-# OPTIONS  --backtracking-instance-search  #-}
module Effect.Hefty.Transact where

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
open import Effect.Nil
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

transact : {H' H'' H''' : EffectH}
           {{w1 : EffectHStorage H (Lift State) H'}}
           {{w2 : EffectHStorage H (Lift Throw) H''}}
           {{w3 : EffectHStorage H       Catch  H'''}}
            -> Hefty H Nat
transact = do
  up (put 1)
  `catch
    (do
      up (put 2)
      b <- (up throw)
      ⊥-elim b)
    (pure tt)
  up get


-- how does it work??
eTransact : Elaboration (Catch +E+ Lift Throw +E+ Lift State +E+ Lift Nil)
            (coProduct Throw (coProduct State Nil))
eTransact = eCatch +A+ eLift +A+ eLift +A+ eNil

test-transact : un ((givenHandle hSt
                   ((givenHandle hThrow
                   (elaborate eTransact transact ))
                   tt) )0) ≡ (just 2 , 2)
test-transact = refl

