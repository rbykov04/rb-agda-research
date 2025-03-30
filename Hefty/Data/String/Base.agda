module Data.String.Base
    where


open import Agda.Builtin.Sigma
open import Agda.Builtin.Char
open import Agda.Builtin.String
open import Agda.Builtin.List
open import Agda.Builtin.Maybe
open import Agda.Builtin.Nat

open import Foundation.Base

{-
  primStringToList   : String → List Char
  primStringFromList : List Char → String
-}

toList = primStringToList
fromList = primStringFromList

length : String → Nat
length str = f (toList str)
    where
    f : List Char -> Nat
    f [] = 0
    f (x ∷ st) = suc (f st)

head : String → Maybe Char
head str = f (toList str)
    where
    f : List Char -> Maybe Char
    f [] = nothing
    f (x ∷ st) = just x

tail : String → Maybe String
tail str = f (toList str)
    where
    f : List Char -> Maybe String
    f [] = nothing
    f (x ∷ st) = just (fromList st )

uncons : String → Maybe ( Char × String )
uncons str = f (toList str)
    where
    f : List Char -> Maybe ( Char × String )
    f [] = nothing
    f (x ∷ st) = just (x , fromList st )
