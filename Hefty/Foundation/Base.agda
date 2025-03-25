module Foundation.Base
    where

open import Agda.Primitive public

infixr 70 _⊎_
data _⊎_ {ℓa ℓb} (A : Set ℓa) (B : Set ℓb) : Set (ℓa ⊔ ℓb) where
  inl : A → A ⊎ B
  inr : B → A ⊎ B

elim : {ℓa ℓb : Level} {A : Set ℓa} {B : Set ℓb}
       {ℓ : Level} {C : A ⊎ B → Set ℓ}
       (f : (a : A) → C (inl a)) (g : (b : B) → C (inr b))
     → (s : A ⊎ B) → C s
elim f _ (inl x) = f x
elim _ g (inr x) = g x
