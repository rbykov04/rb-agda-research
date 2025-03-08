{-# OPTIONS  --backtracking-instance-search  #-}
module Mystdlib.Universe where


-- What is "a universe of types [Martin-Löf 1984]."
-- What does "syntactic type TY" mean?
record Universe : Set₁ where
    field Ty    : Set
          [[_]] : Ty -> Set

open Universe {{...}} public



