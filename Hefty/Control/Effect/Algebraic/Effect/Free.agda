module Control.Effect.Algebraic.Effect.Free
    where

open import Foundation.Base
open import Control.Effect.Algebraic.Effect

data Free {o r ℓ : Level} (Eff : Effect {o} {r}) (A : Set ℓ) : Set (o ⊔ r ⊔ ℓ) where
  pure
    : (a : A)
    → Free Eff A
  impure
    : (op : Op Eff)
    → (k : Ret Eff op → Free Eff A)
    → Free Eff A

Alg
  : {o r a : Level}
  → (Eff : Effect {o} {r})
  → (A : Set a)
  → Set (o ⊔ r ⊔ a)
Alg Eff A = (op : Op Eff) → (k : Ret Eff op → A) → A


fold
  : {o r a b : Level}
  → {Eff : Effect {o} {r}} {A : Set a} {B : Set b}
  → (A → B)
  → (Alg Eff B)
  → Free Eff A
  → B
fold point alg (pure a) = point a
fold point alg (impure op k) = alg op (λ r → fold point alg (k r))

_>>=_
  : {o r a b : Level}
  → {Eff : Effect {o} {r}} {A : Set a} {B : Set b}
  → Free Eff A
  → (A → Free Eff B)
  → Free Eff B
f >>= g = fold g impure f

_>>_
  : {o r a b : Level}
  → {Eff : Effect {o} {r}} {A : Set a} {B : Set b}
  → Free Eff A
  → Free Eff B
  → Free Eff B
f >> g = f >>= λ _ → g

