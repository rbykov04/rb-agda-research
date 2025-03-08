{-# OPTIONS  --backtracking-instance-search  #-}
module Universe where
open import Agda.Builtin.String
open import Agda.Builtin.Unit
open import Agda.Builtin.Maybe
open import Agda.Builtin.Bool
open import Agda.Builtin.List
open import Agda.Builtin.Nat
open import Agda.Builtin.Equality
open import Agda.Builtin.IO
open import Agda.Builtin.Unit
open import Agda.Builtin.String
open import Agda.Builtin.Sigma
open import Agda.Primitive


-- What is "a universe of types [Martin-Löf 1984]."
-- What does "syntactic type TY" mean?
record Universe : Set₁ where
    field Ty    : Set
          [[_]] : Ty -> Set

open Universe {{...}} public



