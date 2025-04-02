
{-# OPTIONS  --backtracking-instance-search  #-}

module Example.Archive.Resource3 where

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
    bracket : Ty ->   ResourceOp

data ResourceBranch  : Set where
  acquire   : ResourceBranch
  release   : String -> ResourceBranch
  inBetween : String -> ResourceBranch



Resource : {{ u : Universe }} -> EffectH
Resource .OpH = ResourceOp
Resource {{u}} .ForkH x .Op = ResourceBranch
Resource .ForkH (bracket t ) .Ret acquire = String
Resource .ForkH (bracket t ) .Ret (release o) = [[ t ]]
Resource .ForkH (bracket t ) .Ret (inBetween x ) = [[ t ]]
Resource .RetH  (bracket t )      = [[ t ]]

`bracket   : {H H' : EffectH}
          -> {{ u : Universe }}
          -> {{ w : EffectHStorage H Resource H' }}
          -> {t : Ty}
          -> Hefty H String
          -> (String -> Hefty H [[ t ]])
          -> (String -> Hefty H [[ t ]])
          -> Hefty H [[ t ]]
`bracket {H} {H'} {{u}} {{ w = w }} {t}  begin end body  =
        impure (inj-left {{w}} (bracket {{u}} t ))
          (proj-fork-l {{w}}  (bracket {{u}} t )  func)
          \ ret -> pure ((proj-ret-l {{w}} ret))
          where
          func : (b : ResourceBranch) → Hefty H (Ret (ForkH Resource (bracket t)) b)
          func acquire = begin
          func (release x) = end x
          func (inBetween x) = body x


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
eResource .alg (bracket x ) fork k = do
      x <- (# givenHandle hOut (fork acquire) tt)
      y <- (# givenHandle hOut (fork $ inBetween (x .fst)) tt)
      z <- (# givenHandle hOut (fork $ release (x .fst)) tt)
      o <- (# givenHandle hOut (k {!!}) tt)
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
  `bracket ( up (out "1") >> pure "Bla")
          (\ str -> up (out str))
          (\ str -> up (out str))
  pure tt
  where open import Effect.Core.Hefty using (_>>=_; _>>_)

test : un (givenHandle hOut (elaborate eee program ) tt) ≡ (tt , "1BlaBla")
test = refl
