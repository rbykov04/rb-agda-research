{-# OPTIONS  --backtracking-instance-search  #-}
module Example.CLang.Branch
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
--open import Control.Effect.Algebraic.Effect.OpenUnion
--open import Control.Effect.Algebraic.Effect.OpenUnion.Properties
open import Control.Effect.Algebraic.Hefty hiding (_>>_ ; _>>=_)
open import Example.CLang.TokenTypes
open import Example.CLang.Effects

private
  variable
    a b c d e : Level
    A : Set a
    B : Set b
    C : Set c
    D : Set d
    E : Set e

data BranchOp : Set1 where
    branch : BranchOp

Branch : HighEffect
Branch .Opᴴ = BranchOp
Branch .Fork x = Nil
Branch .Retᴴ branch = Bool

eBranch : {Effs E1 : Effect}
    → ⦃ effrow Effs ＝ Logger ∣ E1 ⦄
    → Elaboration Branch Effs
eBranch .alg branch fork k = do

    send (log ("bla bla bla"))
    (l1 , x )  <- (# givenHandle hLogger (k true) tt)
    (l2 , y )  <- (# givenHandle hLogger (k false) tt)
    send (log (l1 ++ " and "++ l2))
    eee1 <- k true
    eee2 <- k false
    pure eee2
    where open import Control.Effect.Algebraic.Effect.Free using (_>>=_ ; _>>_)

{-
eBranch : Elaboration Branch (TokenizerResult ⊕ Logger ⊕ TokenThrow)
eBranch .alg branch fork k = do
    o <- k true
    left  <- (givenHandle {!hResult!} (givenHandle {!hLogger!} {!givenHandle ? ?!} {!!}) {!!})
    --left  <- (givenHandle hResult ( givenHandle hLogger (givenHandle hThrow  (k true) tt) tt) tt)
--    left  <- (# givenHandle hResult (# givenHandle hLogger (# givenHandle hThrow  (k true) tt) tt) tt)
 --   rigth <- (# givenHandle hResult (# givenHandle hLogger (# givenHandle hThrow  (k false) tt) tt) tt)

    {!k!}
    where
        open import Control.Effect.Algebraic.Effect.Free using (_>>=_ ; _>>_)
-}
