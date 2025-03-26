module Control.Effect.Algebraic.Effect.OpenUnion.Properties
    where

open import Foundation.Base
open import Control.Effect.Algebraic.Effect
open import Control.Effect.Algebraic.Effect.OpenUnion
open import Control.Effect.Algebraic.Effect.Free

send
  : {o r : Level}
  -> {Eff Effs : Effect {o} {r}}
  -> ⦃ Eff∈Effs : Eff ∈ Effs ⦄
  -> (op : Op Eff)
  -> Free Effs (Ret Eff op)
send ⦃ Eff∈Effs = Eff∈Effs ⦄ op = impure (inject Eff∈Effs op) λ ret → pure (project Eff∈Effs ret)

record Handler {o r a : Level}
                (A : Set a)
                (E : Effect {o} {r})
                (P : Set a)
                (B : Set a)
                (Continue : Effect {o} {r})
                : Set (lsuc (o ⊔ r ⊔ a))
                where
    field ret : A -> P -> Free Continue B
          hdl : Alg E (P -> Free Continue B)
open Handler public

givenHandle : {a b : Level}
            {A : Set b}
            {B : Set b}
            {P : Set b}
            -> {Effs     : Effect {a} {b}}
            -> {X        : Effect {a} {b}}
            -> Handler A X P B Effs
            -> Free (X ⊕ Effs) A
            -> (P -> Free {a} {b} Effs B)
givenHandle h eff = fold (ret h) func eff where
  func : _
  func (inl op) k p = hdl h op k p
  func (inr op) k p = impure op λ x → k x p
