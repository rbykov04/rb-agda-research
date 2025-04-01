module Data.Vec.Base
    where


open import Agda.Builtin.Sigma
open import Agda.Builtin.Char
open import Agda.Builtin.String
open import Agda.Builtin.List
open import Agda.Builtin.Maybe
open import Agda.Builtin.Nat
open import Agda.Primitive

private
  variable
    a b c p : Level
    A : Set a
    B : Set b
    C : Set c



data Vec (A : Set a) : Nat → Set a where
  []  : Vec A zero
  _∷_ : ∀ {n} (x : A) (xs : Vec A n) → Vec A (suc n)

drop : {A : Set a} {n : Nat} → ( m : Nat) → Vec A (m + n) → Vec A n
drop zero [] = []
drop zero (x ∷ xs) = x ∷ xs
drop (suc m) (x ∷ xs) = drop m xs

vecToList : {A : Set a} (n : Nat) → Vec A n → List A
vecToList zero [] = []
vecToList (suc n) (x ∷ xs) = x ∷ vecToList n xs

