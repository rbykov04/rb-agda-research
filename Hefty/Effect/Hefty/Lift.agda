module Effect.Hefty.Lift where

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
open import Hefty hiding (_>>=_; _>>_)

open import Effect.Free.Nil

private
  variable
    a b c d e : Level
    A : Set a
    B : Set b
    C : Set c
    D : Set d
    E : Set e

Lift : Effect -> EffectH
OpH   (Lift x)   = Op x
ForkH (Lift x) _ = Nil
RetH  (Lift x)   = Ret x

{- smart constructor for lift -}
-- FIXME: Rename
up : {E : Effect}
     -> {H H' : EffectH}
     -> {{ w : EffectHStorage H (Lift E) H' }}
     -> (op : Op E)
     -> Hefty H (Ret E op)
up {{w}} op = impure (inj-left {{w}} op)
                     (proj-fork-l {{w}} op (λ ()))
                     \ x → pure (proj-ret-l {{w}} x)
