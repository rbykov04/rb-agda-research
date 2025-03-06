module InstanceArgs where

open import Agda.Builtin.String
open import Agda.Builtin.Nat
open import Agda.Builtin.List
open import Agda.Builtin.Equality

-- https://agda.readthedocs.io/en/latest/language/instance-arguments.html

_++_ : String -> String -> String
a ++ b = primStringAppend a b
infixr 5 _++_

record Show (A : Set) : Set where
    field
        show : A -> String

open Show

instance
    showNat : Show Nat
    show showNat zero = "zero"
    show showNat (suc x) = "suc (" ++ show showNat x ++ ")"

toText : {A : Set} -> {{Show A}} -> A -> String
toText {{sh}} x = show (record { show = show sh }) x

test : toText 1 ≡ "suc (zero)"
test = refl
