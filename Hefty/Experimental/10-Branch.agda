module Experimental.10-Branch
    where

open import Agda.Builtin.Unit
open import Agda.Builtin.Nat
open import Agda.Builtin.Bool
open import Agda.Builtin.String
open import Agda.Builtin.Char
open import Agda.Builtin.List
open import Agda.Primitive
open import Agda.Builtin.Equality
open import Foundation.Base

open import Control.Effect.Algebraic.Effect
open import Control.Effect.Algebraic.Effect.Free
open import Control.Effect.Algebraic.Effect.OpenUnion
open import Control.Effect.Algebraic.Effect.OpenUnion.Properties
open import Control.Effect.Algebraic.FirstOrder.Nil


private
  variable
    a b c d e : Level
    A : Set a
    B : Set b
    C : Set c
    D : Set d
    E : Set e


data BranchOp : Set1
  where
  branch : BranchOp



Branch : FirstEffect
Branch .Op = BranchOp
Branch .Ret branch = Bool

calc0 : { Effs : Effect }
  → ⦃ Branch ∈ Effs ⦄
  → Free Effs Nat
calc0 = pure 30



calc : { Effs : Effect }
  → ⦃ Branch ∈ Effs ⦄
  → Free Effs Nat
calc = do
        mainThread <- send branch
        if mainThread then pure 5 else pure 10

hBranch : {Effs : Effect} -> Handler A Branch ⊤ (Nat) Effs
hBranch .ret x _ = pure 0
hBranch .hdl branch k x = do
  left  <- k true tt
  right <- k false tt
  pure (left + right)


hBranch1 : {Effs : Effect} -> Handler A Branch ⊤ Nat Effs
hBranch1 .ret x _ = pure {!!}
hBranch1 .hdl branch k x = do
  pure 100

test1 : un $ givenHandle hBranch1 calc tt ≡ 100
test1 = refl

hBranch2 : {Effs : Effect} -> Handler Nat Branch ⊤ Nat Effs
hBranch2 .ret x _ = pure x
hBranch2 .hdl branch k x = k true tt

test2 : un $ givenHandle hBranch2 calc tt ≡ 5
test2 = refl

test2' : un $ givenHandle hBranch2 calc0 tt ≡ 30
test2' = refl

hBranch3 : {Effs : Effect} -> Handler Nat Branch ⊤ Nat Effs
hBranch3 .ret x _ = pure x
hBranch3 .hdl branch k op = do
  x <- k true op
  y <- k false op
  pure (x + y)

test3 : un $ givenHandle hBranch3 calc tt ≡ 15
test3 = refl

test3' : un $ givenHandle hBranch3 calc0 tt ≡ 30
test3' = refl

calc3 : { Effs : Effect }
  → ⦃ Branch ∈ Effs ⦄
  → Free Effs Nat
calc3 = do
        mainThread <- send branch
        if mainThread
          then pure 5
          else do
            th1 <- send branch
            if th1
              then pure 10
              else do
                th2 <- send branch
                if th2
                  then
                    pure 15
                  else
                    pure 20

test4 : un $ givenHandle hBranch3 calc3 tt ≡ 50
test4 = refl
