module Effect.Hefty.Catch where

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


open import Effect.Core.Hefty  hiding (_>>=_; _>>_)
open import Effect.Core.Free  hiding (_>>=_; _>>_)
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

-- What is happening???
eCatch : {Eff Eff' : Effect}
        -> {{u : Universe}}
        -> {{w : EffectStorage Eff Throw Eff'}}
        -> Elaboration Catch Eff
alg eCatch (catch t) fork k = do
        res <- (# givenHandle hThrow (fork true) tt)
        case res of \ where
            (just x) -> k x
            nothing -> do
                x <- (fork false)
                k x
  where open import Effect.Core.Free using (_>>=_; _>>_)

data Type : Set where
  unit  : Type
  num   : Type

instance
  TypeUniverse : Universe
  Ty  ⦃ TypeUniverse ⦄ = Type
  [[_]] ⦃ TypeUniverse ⦄ unit = ⊤
  [[_]] ⦃ TypeUniverse ⦄ num  = Nat
