{-# OPTIONS  --backtracking-instance-search  #-}
module Macro where

open import Agda.Builtin.Unit
open import Agda.Builtin.Nat
open import Agda.Builtin.Sigma
open import Agda.Builtin.List
open import Agda.Builtin.Char
open import Agda.Builtin.String
open import Agda.Builtin.IO
open import Agda.Builtin.Equality
open import Agda.Builtin.Reflection
open import Agda.Builtin.List
open import Agda.Primitive

private
  variable
    a b c d e : Level
    A : Set a
    B : Set b
    C : Set c
    D : Set d
    E : Set e


mkArg : {A : Set} -> Visibility -> A -> Arg A
mkArg v = arg (arg-info v (modality relevant quantity-ω))


-- Defining: id-name {A} x = x
defId : (id-name : Name) → TC ⊤
defId id-name = defineFun id-name
  ( clause (
            (   "A", mkArg visible (agda-sort (lit 0) ))
            ∷ ("x", mkArg visible (var 0 []))
            ∷  [])
          (  mkArg  hidden (var 1)
          ∷ mkArg visible (var 0)
          ∷ [])
          (var 0 [])
  ∷ [])

id2 : {A : Set} (x : A) → A
unquoteDef id2 = defId id2


call : Name -> List (Arg Term) -> Arg Term
call f args = mkArg visible (def f args)

callC : Name -> List (Arg Term) -> Arg Term
callC f args = mkArg visible (con f args)


localVar : Nat -> Arg Term
localVar n = mkArg visible (var n [])

[_] : A → List A
[ x ] = x ∷ []


infixl 1 _>>_
_>>=_ : TC A → (A -> TC B) → TC B
t1 >>= t2 = bindTC t1 t2

_>>_ : TC A → TC B → TC B
a >> b = a >>= \ _ → b

mkId : (id-name : Name) → TC ⊤
mkId id-name = do
  ty <- quoteTC ({A : Set} (x : A) → A)
  declareDef (mkArg visible id-name) ty
  defId id-name

unquoteDecl id4 = mkId id4
