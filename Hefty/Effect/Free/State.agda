module Effect.Free.State where

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
open import Effect.Core.Hefty  hiding (_>>=_; _>>_)
open import Effect.Free.Output
open import Effect.Free.Throw
open import Effect.Free.Nil
open import Effect.Hefty.Lift



private
  variable
    a b c d e : Level
    A : Set a
    B : Set b
    C : Set c
    D : Set d
    E : Set e



data StateOp : Set where
    get : StateOp
    put : Nat -> StateOp

State : Effect
Op  State = StateOp
Ret State get = Nat
Ret State (put x) = ⊤

hSt : Handler A State Nat ( A × Nat ) Eff
ret hSt x s = pure (x , s)
hdl hSt get k n = k n n
hdl hSt (put m) k _ = k tt m


`put :
      {E There : Effect}
     -> {{ EffectStorage E State There }}
     -> Nat
     -> Free E ⊤
`put {{ w }} n = impure (inj-insert-left (put n) ) (λ x -> pure (proj-ret-left {{w}} x))

`get :
      {E There : Effect}
     -> {{ EffectStorage E State There }}
     -> Free E Nat
`get {{ w }}  = impure (inj-insert-left get ) (λ x -> pure (proj-ret-left {{w}} x))
