module Experimental.14-Interprete
    where

open import Agda.Builtin.Unit
open import Agda.Builtin.Nat
open import Agda.Builtin.Bool
open import Agda.Builtin.String
open import Agda.Builtin.Char
open import Agda.Builtin.List
open import Agda.Primitive
open import Agda.Builtin.Equality
open import Foundation.Base

open import Control.Effect.Algebraic.Effect
open import Control.Effect.Algebraic.Effect.Free
open import Control.Effect.Algebraic.Effect.OpenUnion
open import Control.Effect.Algebraic.Effect.OpenUnion.Properties
open import Control.Effect.Algebraic.FirstOrder.Nil


private
  variable
    a b c d e : Level
    A : Set a
    B : Set b
    C : Set c
    D : Set d
    E : Set e


data ChoiceOp ( A : Set) : Set1
  where
  choice : List A → ChoiceOp A

Choice : (A : Set) → FirstEffect
Choice A = record
  { Op = ChoiceOp A
  ; Ret = λ where
    (choice _) -> A
  }

hChoice : {Effs : Effect} -> Handler Nat (Choice Nat) ⊤ (List Nat) Effs
hChoice .ret x _ = pure (x ∷ [])
hChoice .hdl (choice []) k op = pure []
hChoice .hdl (choice (n ∷ ns)) k op = do
  x <- k n op
  y <- hChoice .hdl (choice ns) k op
  pure $ appendList x y



interprete' : {a b : Level}
            {A : Set b}
            {B : Set b}
            {P : Set b}
            → {Effs     : Effect {a} {b}}
            → {X        : Effect {a} {b}}
            → Handler A X P B Effs
            → P
            → Free (X ⊕ Effs) A
            → Free {a} {b} Effs B
interprete' h p eff = fold (ret h) func eff p where
  func : _
  func (inl op) k p = hdl h op k p
  func (inr op) k p = impure op λ x → k x p

program1 : List Nat
program1 =  un $ interprete' hChoice tt do
        x <- send $ choice (1 ∷ 2   ∷ [])
        y <- send $ choice (10 ∷ 100 ∷ [])
        pure (x * y)

test1 : program1 ≡ 10 ∷ 100 ∷ 20 ∷ 200 ∷ []
test1 = refl


interprete : {A : Set} {B : Set}
            → {Effs     : FirstEffect}
            → {X        : FirstEffect}
            → Handler A X ⊤ B Effs
            → Free (X ⊕ Effs) A
            → Free Effs B
interprete h eff = fold (λ x → ret h x tt) func eff
  where
    func : _
    func (inl op) k = hdl h op  (λ x _ → k x ) tt
    func (inr op) k = impure op k 



program2 : List Nat
program2 =  un $ interprete hChoice do
        x <- send $ choice (1 ∷ 2   ∷ [])
        y <- send $ choice (10 ∷ 100 ∷ [])
        pure (x * y)

test2 : program2 ≡ 10 ∷ 100 ∷ 20 ∷ 200 ∷ []
test2 = refl
