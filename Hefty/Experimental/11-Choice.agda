module Experimental.11-Choice
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


data ChoiceOp ( A : Set) : Set1
  where
  choice : List A → ChoiceOp A

Choice : (A : Set) → FirstEffect
Choice A = record
  { Op = ChoiceOp A
  ; Ret = λ where
    (choice _) -> A
  }

hChoice : {Effs : Effect} -> Handler Nat (Choice Nat) ⊤ (List Nat) Effs
hChoice .ret x _ = pure (x ∷ [])
hChoice .hdl (choice []) k op = pure []
hChoice .hdl (choice (n ∷ ns)) k op = do
  x <- k n op
  y <- hChoice .hdl (choice ns) k op
  pure $ appendList x y


calc : { Effs : Effect }
  → ⦃ (Choice Nat ) ∈ Effs ⦄
  → Free Effs Nat
calc = do
        x <- send $ choice (1 ∷ 2 ∷ 3 ∷ 4 ∷ [])
        pure (x * 10)

test1 : un $ givenHandle hChoice calc tt ≡ 10 ∷ 20 ∷ 30 ∷ 40 ∷ []
test1 = refl
