module Experimental.12-ChoiceAndThrow
    where

open import Agda.Builtin.Unit
open import Agda.Builtin.Nat
open import Agda.Builtin.Bool
open import Agda.Builtin.Maybe
open import Agda.Builtin.String
open import Agda.Builtin.Char
open import Agda.Builtin.List
open import Agda.Primitive
open import Agda.Builtin.Equality
open import Agda.Builtin.Sigma
open import Data.String.Base
open import Foundation.Base

open import Control.Effect.Algebraic.Effect
open import Control.Effect.Algebraic.Effect.Free
open import Control.Effect.Algebraic.Effect.OpenUnion
open import Control.Effect.Algebraic.Effect.OpenUnion.Properties
open import Control.Effect.Algebraic.FirstOrder.Nil
open import Control.Effect.Algebraic.FirstOrder.Throw


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

hChoice : {Effs : Effect} -> Handler A (Choice Char) ⊤ (List A) Effs
hChoice .ret x _ = pure (x ∷ [])
hChoice .hdl (choice []) k op = pure []
hChoice .hdl (choice (n ∷ ns)) k op = do
  x <- k n op
  y <- hChoice .hdl (choice ns) k op
  pure $ appendList x y

hThrow : {Effs : Effect} -> Handler A (ThrowError String) ⊤ (String ⊎ A) Effs
hThrow .ret x _ = pure $ inr x
hThrow .hdl (throwE code) k x = pure $ inl code

arr = 'a' ∷ 'b' ∷ 'c' ∷ []

calc : { Effs : Effect }
  → ⦃ (Choice Char ) ∈ Effs ⦄
  → ⦃ (ThrowError String ) ∈ Effs ⦄
  → Free Effs ( Char × Char )
calc = do
        x <- send $ choice arr
        y <- send $ choice arr
        pure (x , y)


test1 : un $ givenHandle hChoice (givenHandle hThrow calc tt) tt
          ≡ inr ('a' , 'a')
          ∷ inr ('a' , 'b')
          ∷ inr ('a' , 'c')
          ∷ inr ('b' , 'a')
          ∷ inr ('b' , 'b')
          ∷ inr ('b' , 'c')
          ∷ inr ('c' , 'a')
          ∷ inr ('c' , 'b')
          ∷ inr ('c' , 'c')
          ∷ []
test1 = refl


show : Char -> String
show ch = fromList (ch ∷ [])

calc2 : { Effs : Effect }
  → ⦃ (Choice Char ) ∈ Effs ⦄
  → ⦃ (ThrowError String ) ∈ Effs ⦄
  → Free Effs ( Char × Char )
calc2 = do
        x <- send $ choice arr
        y <- send $ choice arr
        if  primCharEquality x y
          then (do
            x <- send $ throwE ("Ignore " ++ show x ++ " == " ++ show y)
            ⊥-elim x
          ) else pure (x , y)


test2 : un $ givenHandle hChoice (givenHandle hThrow calc2 tt) tt
          ≡ inl "Ignore a == a"
          ∷ inr ('a' , 'b')
          ∷ inr ('a' , 'c')
          ∷ inr ('b' , 'a')
          ∷ inl "Ignore b == b"
          ∷ inr ('b' , 'c')
          ∷ inr ('c' , 'a')
          ∷ inr ('c' , 'b')
          ∷ inl "Ignore c == c"
          ∷ []
test2 = refl
