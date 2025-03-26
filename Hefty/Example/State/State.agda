module Example.State.State where

open import Agda.Builtin.Sigma
open import Agda.Builtin.Unit
open import Agda.Builtin.String
open import Agda.Builtin.Nat
open import Agda.Builtin.Equality

open import Mystdlib.Universe
open import Foundation.Base

open import Control.Effect.Algebraic.Effect
open import Control.Effect.Algebraic.Effect.Free
open import Control.Effect.Algebraic.Effect.OpenUnion
open import Control.Effect.Algebraic.Effect.OpenUnion.Properties

open import Control.Effect.Algebraic.FirstOrder.IO hiding (_>>_ ; _>>=_)
open import Control.Effect.Algebraic.FirstOrder.State
open import Control.Effect.Algebraic.FirstOrder.Nil
open import Control.Effect.Algebraic.FirstOrder.State.OpenUnion
open import Control.Effect.Algebraic.FirstOrder.Teletype
open import Control.Effect.Algebraic.FirstOrder.Teletype.OpenUnion


example1 : Free (State String)   ⊤
example1 = impure (put "str") λ x → pure tt

inc : {Effs : Effect}
  → {{ State Nat ∈ Effs }}
  → Free Effs Nat
inc = do
    x <- send get
    send (put (x + 1))
    pure x


program : Free (Teletype ⊕ State Nat ⊕ IOEF) ⊤
program = do
   i <- inc
   if (i < 10) then (putStrLn "less 10") else (putStrLn "eq 10 or more")


main : IO ⊤
main = exec do
    (st , res) <- (givenHandle hState (givenHandle hTeletype program tt) 10)
    pure res

test-incr :
    un ((givenHandle hState inc ) 10) ≡ (11 , 10)
test-incr = refl

test-incr2 :
    un (runState inc 10) ≡ (11 , 10)
test-incr2 = refl



profState1 : forall (n : Nat) ->
    un (runState inc n) ≡ un (givenHandle hState inc n)
profState1 n = refl
