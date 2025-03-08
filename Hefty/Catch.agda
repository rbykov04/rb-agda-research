module Catch where

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
-- What is maybe
eCatch : {Eff Eff' : Effect}
        -> {{u : Universe}}
        -> {{w : EffectStorage Eff Throw Eff'}}
        -> Elaboration Catch Eff
alg eCatch (catch t) fork k = do
        (just x) <- (# givenHandle hThrow (fork true) tt)
            where -- magic: it is so unintuitive
                nothing -> do
                            x <- (fork false)
                            k x
        k x
  where open import Free using (_>>=_; _>>_)

data Type : Set where
  unit  : Type
  num   : Type

instance
  TypeUniverse : Universe
  Ty  ⦃ TypeUniverse ⦄ = Type
  [[_]] ⦃ TypeUniverse ⦄ unit = ⊤
  [[_]] ⦃ TypeUniverse ⦄ num  = Nat
