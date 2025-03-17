{-# OPTIONS  --backtracking-instance-search  #-}
module Effect.Free2.State where

open import Agda.Builtin.Unit
open import Agda.Builtin.Sigma
open import Agda.Builtin.List
open import Agda.Builtin.Char
open import Agda.Builtin.String
open import Agda.Builtin.IO
open import Agda.Builtin.Equality
open import Agda.Primitive

open import Mystdlib.Mystdlib

open import Effect.Core.Free2

private
  variable
    a b c d e : Level
    A : Set a
    B : Set b
    C : Set c
    D : Set d
    E : Set e
data StateOp : Set1 where
    get : StateOp
    put : Char -> StateOp

State : Effect2
Op  State = StateOp
Ret State get = Char
Ret State (put x) = ⊤

hSt : {Eff : Effect2} -> Handler2 A State Char ( A × Char ) Eff
ret hSt x s = pure (x , s)
hdl hSt get k n = k n n
hdl hSt (put m) k _ = k tt m


`put :
      {E There : Effect2}
     -> {{ EffectStorage2 E State There }}
     -> Char
     -> Free2 E ⊤
`put {{ w }} n = impure (inj-insert-left2 (put n) ) (λ x -> pure (proj-ret-left2 {{w}} x))

`get :
      {E There : Effect2}
     -> {{ EffectStorage2 E State There }}
     -> Free2 E Char
`get {{ w }}  = impure (inj-insert-left2 get ) (λ x -> pure (proj-ret-left2 {{w}} x))
