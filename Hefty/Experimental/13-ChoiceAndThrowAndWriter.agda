module Experimental.13-ChoiceAndThrowAndWriter
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

data WriterOp ( A : Set ) : Set1
  where
  tell : A → WriterOp A

Writer : (A : Set) → FirstEffect
Writer A .Op = WriterOp A
Writer A .Ret (tell x) = ⊤

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

hWriter : {Effs : Effect} -> Handler A (Writer String) ⊤ (String × A) Effs
hWriter .ret x _ = pure ("" , x)
hWriter .hdl (tell text) k p = do
  ( xs , res ) <- k tt p
  pure ((text ++ xs) , res)

arr = 'a' ∷ 'b' ∷ 'c' ∷ []


show : Char -> String
show ch = fromList (ch ∷ [])

calc : { Effs : Effect }
  → ⦃ (Writer String ) ∈ Effs ⦄
  → ⦃ (Choice Char ) ∈ Effs ⦄
  → ⦃ (ThrowError String ) ∈ Effs ⦄
  → Free Effs ( Char × Char )
calc = do
        send $ tell "Start "
        x <- send $ choice arr
        send $ tell ("(" ++ show x)
        y <- send $ choice arr
        send $ tell (" + " ++ show y ++ ")")
        pure (x , y)


test1 : un $ givenHandle hWriter (givenHandle hChoice (givenHandle hThrow calc tt) tt) tt
          ≡ ("Start (a + a) + b) + c)(b + a) + b) + c)(c + a) + b) + c)"
             , inr ('a' , 'a')
              ∷ inr ('a' , 'b')
              ∷ inr ('a' , 'c')
              ∷ inr ('b' , 'a')
              ∷ inr ('b' , 'b')
              ∷ inr ('b' , 'c')
              ∷ inr ('c' , 'a')
              ∷ inr ('c' , 'b')
              ∷ inr ('c' , 'c')
              ∷ [])
test1 = refl

test1' : un $ givenHandle hChoice (givenHandle hWriter (givenHandle hThrow calc tt) tt) tt
          ≡     ( "Start (a + a)" , inr ('a' , 'a'))
              ∷ ( "Start (a + b)", inr ('a' , 'b'))
              ∷ ( "Start (a + c)", inr ('a' , 'c'))
              ∷ ( "Start (b + a)", inr ('b' , 'a'))
              ∷ ( "Start (b + b)", inr ('b' , 'b'))
              ∷ ( "Start (b + c)", inr ('b' , 'c'))
              ∷ ( "Start (c + a)", inr ('c' , 'a'))
              ∷ ( "Start (c + b)", inr ('c' , 'b'))
              ∷ ( "Start (c + c)", inr ('c' , 'c'))
              ∷ []
test1' = refl





calc2 : { Effs : Effect }
  → ⦃ (Writer String ) ∈ Effs ⦄
  → ⦃ (Choice Char ) ∈ Effs ⦄
  → ⦃ (ThrowError String ) ∈ Effs ⦄
  → Free Effs ( Char × Char )
calc2 = do
        send $ tell "Start "
        x <- send $ choice arr
        send $ tell ("(" ++ show x)
        y <- send $ choice arr
        send $ tell (" + " ++ show y)
        if  primCharEquality x y
          then (do
            send $ tell (" !fail)")
            x <- send $ throwE ("Ignore " ++ show x ++ " == " ++ show y)
            ⊥-elim x
          ) else do
            send $ tell (" !ok)")
            pure (x , y)


test2 : un $ givenHandle hWriter (givenHandle hChoice (givenHandle hThrow calc2 tt) tt) tt
          ≡ ("Start (a + a !fail) + b !ok) + c !ok)(b + a !ok) + b !fail) + c !ok)(c + a !ok) + b !ok) + c !fail)"
          , inl "Ignore a == a"
          ∷ inr ('a' , 'b')
          ∷ inr ('a' , 'c')
          ∷ inr ('b' , 'a')
          ∷ inl "Ignore b == b"
          ∷ inr ('b' , 'c')
          ∷ inr ('c' , 'a')
          ∷ inr ('c' , 'b')
          ∷ inl "Ignore c == c"
          ∷ [] )
test2 = refl


test2' : un $ givenHandle hChoice (givenHandle hWriter (givenHandle hThrow calc2 tt) tt) tt
          ≡     ( "Start (a + a !fail)" , inl "Ignore a == a")
              ∷ ( "Start (a + b !ok)", inr ('a' , 'b'))
              ∷ ( "Start (a + c !ok)", inr ('a' , 'c'))
              ∷ ( "Start (b + a !ok)", inr ('b' , 'a'))
              ∷ ( "Start (b + b !fail)", inl "Ignore b == b")
              ∷ ( "Start (b + c !ok)", inr ('b' , 'c'))
              ∷ ( "Start (c + a !ok)", inr ('c' , 'a'))
              ∷ ( "Start (c + b !ok)", inr ('c' , 'b'))
              ∷ ( "Start (c + c !fail)", inl "Ignore c == c")
              ∷ []
test2' = refl


test2'' : un $ givenHandle hThrow (givenHandle hChoice (givenHandle hWriter calc2 tt) tt) tt ≡ inl ("Ignore a == a")
test2'' = refl
