module Foundation.Base
    where

open import Agda.Primitive public
open import Agda.Builtin.Bool
open import Agda.Builtin.String
open import Agda.Builtin.Unit
open import Agda.Builtin.Maybe
open import Agda.Builtin.Nat
open import Agda.Builtin.Equality
open import Agda.Builtin.IO
open import Agda.Builtin.Unit
open import Agda.Builtin.Sigma
open import Agda.Primitive




private
  variable
    a b c d e : Level
    A : Set a
    B : Set b
    C : Set c
    D : Set d
    E : Set e



infixr 70 _⊎_
data _⊎_ {ℓa ℓb} (A : Set ℓa) (B : Set ℓb) : Set (ℓa ⊔ ℓb) where
  inl : A → A ⊎ B
  inr : B → A ⊎ B

elim : {ℓa ℓb : Level} {A : Set ℓa} {B : Set ℓb}
       {ℓ : Level} {C : A ⊎ B → Set ℓ}
       (f : (a : A) → C (inl a)) (g : (b : B) → C (inr b))
     → (s : A ⊎ B) → C s
elim f _ (inl x) = f x
elim _ g (inr x) = g x

infix 0 if_then_else_

if_then_else_ : Bool → A → A → A
if true  then t else f = t
if false then t else f = f

case_of_ : A -> (A -> B) -> B
case x of f = f x


infixr 12 _++_
_++_ : String -> String -> String
a ++ b = primStringAppend a b

data ⊥ : Set where
⊥-elim : ∀ {w} {Whatever : Set w} → ⊥ → Whatever
⊥-elim ()

---
-- also know as ( , )
infixr 2 _×_
_×_ : ∀ (A : Set a) (B : Set b) → Set (a ⊔ b)
_×_ {a} {b} A B = Σ A (λ x -> B)


id : A -> A
id x = x

_$_ : ∀ {A : Set a} {B : A → Set b} →
      ((x : A) → B x) → ((x : A) → B x)
f $ x = f x
{-# INLINE _$_ #-}
