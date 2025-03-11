module Effect.Free.Nil where

open import Agda.Builtin.String
open import Agda.Builtin.Unit
open import Agda.Builtin.Maybe
open import Agda.Builtin.Bool
open import Agda.Builtin.List
open import Agda.Builtin.Nat
open import Agda.Builtin.IO
open import Agda.Builtin.Unit
open import Agda.Builtin.String
open import Agda.Builtin.Sigma
open import Agda.Primitive

open import Mystdlib.Mystdlib
open import Mystdlib.Universe

open import Effect.Core.Free  hiding (_>>=_; _>>_)

private
  variable
    a b c d e : Level
    A : Set a
    B : Set b
    C : Set c
    D : Set d
    E : Set e


Nil : Effect
Op  Nil = ⊥
Ret Nil = ⊥-elim

un : Free Nil A -> A
un (pure x) = x
