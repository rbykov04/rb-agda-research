module Control.Effect.Algebraic.Effect.OpenUnion
    where

open import Foundation.Base
open import Control.Effect.Algebraic.Effect

data _∈_ {o r : Level} : (Effect {o} {r}) -> (Effect {o} {r}) -> Set (lsuc (o ⊔ r)) where
   reflex
    :  {x  : Effect {o} {r}}
    -> x ∈ x
   insert
    :  {x  : Effect {o} {r}}
    -> {y : Effect {o} {r}}
    -> x ∈ (x ⊕ y)
   sift
    :  {x  : Effect {o} {r}}
    -> {y : Effect {o} {r}}
    -> {z : Effect {o} {r}}
    -> x ∈ y
    -> x ∈ (z ⊕ y)
infix 4 _∈_

instance
  Effect-∈-here
    :  {o r : Level }
    -> {Eff : Effect {o} {r}}
    -> Eff ∈ Eff
  Effect-∈-here = reflex
  {-# OVERLAPS Effect-∈-here #-}

  Effect-∈-inl
    :  {o r : Level }
    -> {Eff Effs : Effect {o} {r}}
    -> Eff ∈ Eff ⊕ Effs
  Effect-∈-inl = insert 
  {-# OVERLAPS Effect-∈-inl #-}

  Effect-∈-inr
    :  {o r : Level }
    -> {Eff' Eff Effs : Effect {o} {r}}
    -> ⦃ Eff∈Effs : Eff ∈ Effs ⦄
    -> Eff ∈ Eff' ⊕ Effs
  Effect-∈-inr ⦃ Eff∈Effs ⦄ = sift Eff∈Effs
  {-# OVERLAPS Effect-∈-inr #-}
inject
  : {o r : Level}
  → {Eff : Effect {o} {r}} {Effs : Effect {o} {r}}
  → (w : Eff ∈ Effs)
  → (op : Op Eff)
  → Op Effs
inject reflex x   = x
inject insert op   = inl op
inject (sift w) op = inr (inject w op)

project
  : {o r : Level}
  → {Eff : Effect {o} {r}} {Effs : Effect {o} {r}}
  → (w : Eff ∈ Effs)
  → {op : Op Eff}
  → (ret : Ret Effs (inject w op))
  → Ret Eff op
project reflex ret   = ret
project insert ret   = ret
project (sift w) ret = project w ret
