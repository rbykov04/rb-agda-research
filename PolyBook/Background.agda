{-# OPTIONS --cubical #-}
module Background where

open import Agda.Builtin.Nat
open import Agda.Builtin.Bool

open import Agda.Primitive
open import Agda.Primitive.Cubical
open import Agda.Builtin.Cubical.Path
open import Agda.Builtin.Unit


data ⊥ : Set where
⊥-elim : ∀ {w} {Whatever : Set w} → ⊥ → Whatever
⊥-elim ()



private variable
  ℓ ℓr : Level
  A B C : Set ℓ
  w x y z : A
  n k : Nat
  P : A → Set ℓ
  Q : (x : A) → P x → Set ℓ

infix 0 if_then_else_

if_then_else_ : Bool → A → A → A
if true  then t else f = t
if false then t else f = f

natOrBool : (b : Bool) -> if b then Nat else Bool
natOrBool false = true
natOrBool true  = 0

unit : {A : Set} -> A -> ⊤
unit _ = tt

absurd : {A : Set} -> ⊥ -> A
absurd ()

--HOW?????? what is i ?
funExt : {f g : A → B} (h : ∀ x → f x ≡ g x) → f ≡ g
funExt h = \ i -> \ x -> h x i

absurdUnique : {A : Set} -> ( f : ⊥ -> A ) -> f ≡ absurd
absurdUnique f = funExt lemma
    where
        lemma : (x : ⊥) -> f x ≡ absurd x
        lemma = λ ()
