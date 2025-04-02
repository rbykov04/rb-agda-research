module Experimental.9-TermCheck
    where

open import Agda.Builtin.Unit
open import Agda.Builtin.Nat
open import Agda.Builtin.String
open import Agda.Builtin.Char
open import Agda.Builtin.List
open import Agda.Primitive

private
  variable
    a b c p : Level
    A : Set a
    B : Set b
    C : Set c





drop : {A : Set} → Nat → List A → List A
drop n [] = []
drop zero (x ∷ xs) = x ∷ xs
drop (suc n) (x ∷ xs) = drop n xs

ok : Nat  -> List Char → ⊤
ok n [] = tt
ok n (x ∷ xs) = ok n xs

module Problem where

    {-# TERMINATING #-}
    problem : Nat  -> List Char → ⊤
    problem n [] = tt
    problem n (x ∷ xs) = problem n (drop 0 xs)

data Vec (A : Set a) : Nat → Set a where
  []  : Vec A zero
  _∷_ : ∀ {n} (x : A) (xs : Vec A n) → Vec A (suc n)

dropVec : {A : Set a} {n : Nat} → ( m : Nat) → Vec A (m + n) → Vec A n
dropVec zero [] = []
dropVec zero (x ∷ xs) = x ∷ xs
dropVec (suc m) (x ∷ xs) = dropVec m xs

problem : {m : Nat} →  Nat  -> Vec Char m  → ⊤
problem n [] = tt
problem n (x ∷ xs) = problem n (dropVec 0 xs)


-- https://github.com/sergei-romanenko/agda-samples/blob/master/08-WellFounded.agda

add : Nat → Nat → Nat
add zero y = y
add (suc x) y = suc ( add x y )

data Bin : Set where
  ε  : Bin
  c0 : Bin → Bin
  c1 : Bin → Bin


foo : Bin -> Nat
foo ε = zero
foo (c0 ε) = zero
foo (c0 (c1 x)) = suc (foo (c0 x))
foo (c0 (c0 x)) = suc (foo (c0 x))
foo (c1 x) = suc (foo x)
{-
log2 : Nat → Nat
log2 zero = zero
log2 (suc zero) = zero
log2 (suc (suc x)) = suc (log2 (suc {!!}))
-}
