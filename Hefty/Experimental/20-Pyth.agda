{-
https://github.com/sayo-hs/heftia/blob/7ffbdba806f9832f9fc3bbed7581537df6d1b6fc/heftia-effects/test/Test/Pyth.hs#L8
-}
module Experimental.20-Pyth
    where

open import Agda.Builtin.Unit
open import Agda.Builtin.Nat
open import Agda.Builtin.Bool
open import Agda.Builtin.Maybe
open import Agda.Builtin.String
open import Agda.Builtin.Char
open import Agda.Builtin.List
open import Agda.Primitive
open import Agda.Builtin.Equality
open import Agda.Builtin.Sigma
open import Data.String.Base
open import Foundation.Base

open import Control.Effect.Algebraic.Effect
open import Control.Effect.Algebraic.Effect.Free
  hiding ( _>>_)
  renaming
    ( _>>=_ to _>>=Free_
    ; pure to pureFree
    )
open import Control.Effect.Algebraic.Effect.OpenUnion
open import Control.Effect.Algebraic.Effect.OpenUnion.Properties
open import Control.Effect.Algebraic.FirstOrder.Nil
open import Control.Effect.Algebraic.FirstOrder.Throw


private
  variable
    a b c d e f g : Level
    A B C : Set f
    Effs : FirstEffect

record Functor {f g : Level} (F : Set f  → Set g) : Set (lsuc f ⊔ g)
  where
  infixl 1 _<$_
  field
        fmap : (A → B) → F A → F B

  _<$_ : A → F B → F A
  a <$ fb = fmap (λ _ → a) fb


record Applicative {f g : Level} (F : Set f  → Set g) : Set (lsuc f ⊔ g)
  where
  infixl 4 _<*>_
  field functor : Functor F
        pure : A  → F A
        _<*>_ : F (A → B) → F A → F B

  open Functor functor public


  liftA2 : ( A -> B -> C ) → F A → F B → F C
  liftA2 f x y = fmap f x <*> y

record Alternative {f g : Level} (F : Set f  → Set g) : Set (lsuc (f ⊔ g))
  where
  infixl 4 _<|>_
  field applicative : Applicative F
        empty : F A
        _<|>_ : F A → F A → F A
  open Applicative applicative public




record Monad {f g : Level} (F : Set f  → Set g) : Set (lsuc (f ⊔ g))
  where
  infixl 1 _>>=_ _>>_
  field
        applicative : Applicative F
        _>>=_ : F A → ( A → F B) → F B

  open Applicative applicative public

  _>>_  : F A → F B → F B
  x >> y =  x >>= λ _ → y

  return : A → F A
  return = pure

--open Monad {{...}} public

record MonadPlus {f g : Level} (F : Set f → Set g) : Set (lsuc (f ⊔ g))
  where
  field
    alternative : Alternative F
    monad : Monad F
    mzero : F A
    mplus : F A -> F A → F A

  open Alternative alternative public
  open Monad monad public hiding (_<$_ ; liftA2)

open MonadPlus {{...}}


instance
  FreeMonad  : {o r ℓ : Level}
    {E : Effect {o} {r} } → Monad {ℓ} {o ⊔ r ⊔ ℓ} (Free {o} {r} {ℓ} E)
  FreeMonad = record
    { applicative = record
      { functor = record
        { fmap = λ f x → fold (λ x₁ → pureFree (f x₁)) impure x
        }
      ; pure = pureFree
      ; _<*>_ = λ fab a → fab >>=Free λ x → a >>=Free λ z → pureFree (x z)
      }
    ; _>>=_ = _>>=Free_
    }



search : {f g : Level}
        → {M : Set → Set g}
        → {{ MonadPlus M }} → Nat → M (Nat × Nat × Nat)
search {f} {g} {M} ⦃ x ⦄ unbound = do
  x <- choice unbound
  y <- choice unbound
  z <- choice unbound
  if (x * x + y * y == z * z)
    then return (( x , (y  , z ) ))
    else empty
  empty
  where
    choice : Nat → M Nat
    choice zero = empty
    choice (suc x) = choice x <|> return x

data EmptyOp (A : Set) : Set1
  where
  emptyOp : A → EmptyOp A

Empty : (A : Set) → FirstEffect
Empty A = record
  { Op = EmptyOp A
  ; Ret = λ where
    (emptyOp _) -> A
  }

{-
instance
  foo  : {o r ℓ : Level}
    {E : Effect {o} {r} } → MonadPlus {ℓ} {o ⊔ r ⊔ ℓ} (Free {o} {r} {ℓ} E)
  foo = {!!}

data ChooseOp ( A : Set) : Set1
  where
  choose : A → ChooseOp A


Choose : (A : Set) → FirstEffect
Choose A = record
  { Op = ChooseOp A
  ; Ret = λ where
    (choose _) -> A
  }
-}
