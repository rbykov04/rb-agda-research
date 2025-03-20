{-
Like:
https://hackage.haskell.org/package/data-effects-0.3.0.1/docs/src/Data.Effect.Resource.html#Resource
An effect capable of providing [bracket]
(https://hackage.haskell.org/package/base-4.16.4.0/docs/Control-Exception.html#v:bracket) semantics.
-}

{-# OPTIONS  --backtracking-instance-search  #-}

module Example.Resource2 where

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
open import Effect.Core.Hefty  hiding (_>>=_; _>>_)
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
  str   : Type

data ResourceOp {{ u : Universe }} : Set where
    bracket : Ty -> Ty ->  ResourceOp

data ResourceBranch : Set where
  acquire   : ResourceBranch
  release   : ResourceBranch
  inBetween : ResourceBranch



Resource : {{ u : Universe }} -> EffectH
Resource .OpH = ResourceOp
Resource .ForkH x .Op            = ResourceBranch
Resource .ForkH (bracket t s) .Ret acquire = [[ s ]]
Resource .ForkH (bracket t s) .Ret release = [[ t ]]
Resource .ForkH (bracket t s) .Ret inBetween = [[ t ]]
Resource .RetH  (bracket t s)      = [[ t ]]

`bracket   : {H H' : EffectH}
          -> {{ u : Universe }}
          -> {{ w : EffectHStorage H Resource H' }}
          -> {t : Ty}
          -> {str : Ty}
          -> Hefty H [[ str ]]
          -> (Hefty H [[ str ]] -> Hefty H [[ t ]])
          -> (Hefty H [[ str ]] -> Hefty H [[ t ]])
          -> Hefty H [[ t ]]
`bracket {H} {H'} {{u}} {{ w = w }} {t} {s} begin end body  =
        impure (inj-left {{w}} (bracket t s))
          (proj-fork-l {{w}}  (bracket t s)  func)
          \ ret -> pure ((proj-ret-l {{w}} ret))
          where
          func : (b : ResourceBranch) → Hefty H (Ret (ForkH Resource (bracket t s)) b)
          func acquire = begin
          func release = end begin
          func inBetween = body begin
{-
`bracket   : {H H' : EffectH}
          -> {{ u : Universe }}
          -> {{ w : EffectHStorage H Resource H' }}
          -> {t : Ty}
          -> {str : Ty}
          -> Hefty H [[ str ]]
          -> ([[ str ]] -> Hefty H [[ t ]])
          -> ([[ str ]] -> Hefty H [[ t ]])
          -> Hefty H [[ t ]]
`bracket {H} {H'} {{u}} {{ w = w }} {t} {s} begin end body  =
        impure (inj-left {{w}} (bracket t s))
          (proj-fork-l {{w}}  (bracket t s)  func)
          \ ret -> pure ((proj-ret-l {{w}} ret))
          where
          func : (b : ResourceBranch) → Hefty H (Ret (ForkH Resource (bracket t s)) b)
          func acquire = begin
          func release = end {!!}
          func inBetween = body _
-}



instance
  TypeUniverse : Universe
  Ty  ⦃ TypeUniverse ⦄ = Type
  [[_]] ⦃ TypeUniverse ⦄ unit = ⊤
  [[_]] ⦃ TypeUniverse ⦄ num  = Nat
  [[_]] ⦃ TypeUniverse ⦄ str  = String

eResource : {Eff Eff' : Effect}
        -> {{u : Universe}}
        -> {{w : EffectStorage Eff Output Eff'}}
        -> Elaboration (Resource {{u}}) Eff
eResource .alg (bracket x s) fork k = do
      x <- (# givenHandle hOut (fork acquire) tt)
      y <- (# givenHandle hOut (fork inBetween) tt)
      z <- (# givenHandle hOut (fork release) tt)
      `out (x .snd)
      `out (y .snd)
      `out (z .snd)
      k (y .fst)
    where open import Effect.Core.Free using (_>>=_; _>>_)

eee : Elaboration (Resource +E+  Lift Output +E+ Lift Nil)
                  (Output |> Nil)
eee = eResource +A+ eLift +A+  eNil

program : {H There1 There2 : EffectH}
          {{w1 : EffectHStorage H (Lift Output) There1}}
          {{w2 : EffectHStorage H      Resource There2}}
           -> Hefty H ⊤
program = do
  `bracket (pure "Bla")
          (\ s -> s >>= \ str -> up (out str))
          (\ s -> s >>= \ str -> up (out str))
  pure tt
  where open import Effect.Core.Hefty using (_>>=_; _>>_)


test : un (givenHandle hOut (elaborate eee program ) tt) ≡ (tt , "BlaBla")
test = refl



program2 : {H There1 : EffectH}
          {{w3 : EffectHStorage H (Lift Output) There1}}
           -> Hefty H ⊤
program2 = do
  (up (out "{"))
  (up (out "bla"))
  (up (out "}"))
  pure tt
  where open import Effect.Core.Hefty using (_>>=_; _>>_)

eee1 : Elaboration (Lift Output +E+ Lift Nil)
                  (Output |> Nil)
eee1 = eLift +A+ eNil



test-2 : un (givenHandle hOut (elaborate eee1 program2 ) tt) ≡ (tt , "{bla}")
test-2 = refl

{-
program : {H There1 There2 : EffectH}
          {{w1 : EffectHStorage H (Lift Output) There1}}
          {{w2 : EffectHStorage H      Resource There2}}
           -> Hefty H ⊤
program = do
  `bracket (pure "Bla")
          (\ str -> up (out str))
          (\ str -> up (out str))
  pure tt
  where open import Effect.Core.Hefty using (_>>=_; _>>_)
-}
