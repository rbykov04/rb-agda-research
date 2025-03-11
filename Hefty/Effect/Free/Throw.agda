module Effect.Free.Throw where

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

open import Free  hiding (_>>=_; _>>_)

private
  variable
    a b c d e : Level
    A : Set a
    B : Set b
    C : Set c
    D : Set d
    E : Set e

data ThrowOp : Set where
    throw : ThrowOp

Throw : Effect
Op Throw = ThrowOp
Ret Throw throw = ⊥

--Rethink this
`throw : {E There : Effect}
     -> {{ EffectStorage E Throw There }}
     -> Free E A
`throw {{ w }} = impure (inj-insert-left throw ) (λ x -> ⊥-elim (proj-ret-left {{w}} x))

hThrow : Handler A Throw ⊤ (Maybe A) Eff
ret hThrow x _ = pure (just x)
hdl hThrow throw _ _ = pure nothing
