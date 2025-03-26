module Control.Effect.Algebraic.FirstOrder.Nil
    where

open import Foundation.Base

open import Control.Effect.Algebraic.Effect
open import Control.Effect.Algebraic.Effect.Free

private
  variable
    a b c d e : Level
    A : Set a
    B : Set b
    C : Set c
    D : Set d
    E : Set e


data NilOp : Set1 where

Nil : Effect {lsuc lzero} {lzero}
Op  Nil = NilOp
Ret Nil = λ ()

un : Free Nil A -> A
un (pure x) = x
