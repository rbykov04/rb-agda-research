
{-# OPTIONS --exact-split #-}
{-# OPTIONS  --backtracking-instance-search  #-}
module Main where

open import Agda.Builtin.String
open import Agda.Builtin.Unit
open import Agda.Builtin.Bool
open import Agda.Builtin.List
open import Agda.Builtin.Nat
open import Agda.Builtin.Equality
open import Agda.Builtin.IO
open import Agda.Builtin.Unit
open import Agda.Builtin.String
open import Agda.Builtin.Sigma
open import Agda.Primitive

open import Free hiding (_>>=_; _>>_)
open import Hefty

private
  variable
    a b c d e : Level
    A : Set a
    B : Set b
    C : Set c
    D : Set d
    E : Set e

infix 0 if_then_else_

if_then_else_ : Bool → A → A → A
if true  then t else f = t
if false then t else f = f

-- What is "a universe of types [Martin-Löf 1984]."
-- What does "syntactic type TY" mean?
record Universe : Set₁ where
    field Ty    : Set
          [[_]] : Ty -> Set

open Universe {{...}} public



data CatchOp {{ u : Universe }} : Set where
    catch : Ty -> CatchOp

-- How does it work?
Catch : {{ u : Universe }} -> EffectH
OpH   Catch = CatchOp
ForkH Catch (catch t) = record
    { Op = Bool -- why is bool here?
    ; Ret = \ _ → [[ t ]] }
RetH Catch (catch t) = [[ t ]]


`catch   : {H H' : EffectH}
          -> {{ u : Universe }}
          -> {{ w : EffectHStorage H Catch H' }}
          -> {t : Ty}
          -> Hefty H [[ t ]]
          -> Hefty H [[ t ]]
          -> Hefty H [[ t ]]
`catch  {{ w = w }}  m1 m2  =
    impure
        (inj-left {{w}} (catch _))
        (proj-fork-l {{w}} _ λ b → if b then m1 else m2)
        \ ret → pure ((proj-ret-l {{w}} ret))

data Type : Set where
  unit  : Type
  num   : Type

instance
  TypeUniverse : Universe
  Ty  ⦃ TypeUniverse ⦄ = Type
  [[_]] ⦃ TypeUniverse ⦄ unit = ⊤
  [[_]] ⦃ TypeUniverse ⦄ num  = Nat


transact : {H H' H0 H'' : EffectH}
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
