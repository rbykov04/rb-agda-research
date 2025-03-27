{-# OPTIONS  --backtracking-instance-search  #-}
module Example.Hefty.Catch where

open import Agda.Builtin.String
open import Agda.Builtin.Unit
open import Agda.Builtin.Maybe
open import Agda.Builtin.Bool
open import Agda.Builtin.List
open import Agda.Builtin.Nat
open import Agda.Builtin.IO
open import Agda.Builtin.Unit
open import Agda.Builtin.String
open import Agda.Builtin.Equality
open import Agda.Builtin.Sigma
open import Agda.Primitive

open import Mystdlib.Mystdlib
open import Mystdlib.Universe


open import Effect.Core.Free  hiding (_>>=_; _>>_)
open import Effect.Free.Output
open import Effect.Free.Throw
open import Effect.Free.Nil
open import Effect.Nil
open import Effect.Free.State Nat
open import Effect.Hefty.Lift
open import Effect.Hefty.Catch
open import Effect.Core.Hefty

private
  variable
    a b c d e : Level
    A : Set a
    B : Set b
    C : Set c
    D : Set d
    E : Set e


eTransact : Elaboration (Lift State +E+ Lift Throw +E+ Catch +E+ Lift Nil)
              (State |> Throw |> Nil)
eTransact = eLift +A+ eLift +A+ eCatch +A+ eNil

transact : {Row H' H'' H''' : EffectH}
           -> {{heftyrow Row ＝ Catch      ∣ H'''}}
           -> {{heftyrow Row ＝ Lift State ∣ H'}}
           -> {{heftyrow Row ＝ Lift Throw ∣ H''}}
            -> Hefty Row Nat
transact = do
  up (put 1)
  `catch
    (do
      up (put 2)
      b <- (up throw)
      ⊥-elim b)
    (pure tt)
  up get

test-transact : un ((givenHandle hSt
                   ((givenHandle hThrow
                   (elaborate eTransact transact ))
                   tt) )0) ≡ (just 2 , 2)
test-transact = refl

