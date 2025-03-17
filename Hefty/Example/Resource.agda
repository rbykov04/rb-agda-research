{-
Like:
https://hackage.haskell.org/package/data-effects-0.3.0.1/docs/src/Data.Effect.Resource.html#Resource
An effect capable of providing [bracket]
(https://hackage.haskell.org/package/base-4.16.4.0/docs/Control-Exception.html#v:bracket) semantics.
-}

{-# OPTIONS  --backtracking-instance-search  #-}

module Example.Resource where

open import Agda.Builtin.Unit
open import Agda.Builtin.Sigma
open import Agda.Builtin.List
open import Agda.Builtin.Char
open import Agda.Builtin.String
open import Agda.Builtin.IO
open import Agda.Builtin.Equality
open import Agda.Primitive
open import Agda.Builtin.Nat

open import Mystdlib.Mystdlib
open import Mystdlib.Universe


open import Effect.Core.Free hiding (_>>=_; _>>_)
open import Effect.Core.Hefty
open import Effect.Free.Output
open import Effect.Free.Nil
open import Effect.Free.State String
open import Effect.Free.Output
open import Effect.Free.Throw
open import Effect.Free.Nil
open import Effect.Nil
open import Effect.Hefty.Lift
open import Agda.Builtin.Bool
private
  variable
    a b c d e : Level
    A : Set a
    B : Set b
    C : Set c
    D : Set d
    E : Set e

--data ResourceOp {{ u : Universe }} : Set where
--    Bracket : Ty -> ResourceOp
data Type : Set where
  unit  : Type
  num   : Type

data ResourceOp {{ u : Universe }} : Set where
    bracket : Ty -> Ty -> Ty ->  ResourceOp

-- How does it work?
Resource : {{ u : Universe }} -> EffectH
Resource .OpH = ResourceOp
Resource .ForkH = {!!}
Resource .RetH (bracket acquire release between) = {!!}

`bracket   : {H H' : EffectH}
          -> {{ u : Universe }}
          -> {{ w : EffectHStorage H Resource H' }}
          -> {t : Ty}
          -> Hefty H [[ t ]]
          -> Hefty H [[ t ]]
          -> Hefty H [[ t ]]
          -> Hefty H [[ t ]]
`bracket  {{ w = w }}  acquire release between  = {!!}
{-
    impure
        (inj-left {{w}} (catch _))
        (proj-fork-l {{w}} _ λ b → if b then m1 else m2)
        \ ret → pure ((proj-ret-l {{w}} ret))
-}


instance
  TypeUniverse : Universe
  Ty  ⦃ TypeUniverse ⦄ = Type
  [[_]] ⦃ TypeUniverse ⦄ unit = ⊤
  [[_]] ⦃ TypeUniverse ⦄ num  = Nat

program : {H There1 There2 There3 There4 : EffectH}
          {{w1 : EffectHStorage H (Lift State)  There1}}
          {{w2 : EffectHStorage H (Lift Throw)  There2}}
          {{w3 : EffectHStorage H (Lift Output) There3}}
          {{w4 : EffectHStorage H       Resource   There4}}
           -> Hefty H String
program = do
  `bracket
    (up (out "{"))
    (up (out "}"))
    (do
      (up (out "Main text are here"))
      (up (out "Main text are here"))
      (up (out "Main text are here"))
      )
  up get
