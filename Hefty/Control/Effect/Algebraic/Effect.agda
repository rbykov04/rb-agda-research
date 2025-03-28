module Control.Effect.Algebraic.Effect
    where

open import Foundation.Base

record Effect {o r : Level} : Set (lsuc (o ⊔ r)) where -- (a ⊔ b) where
 field Op  : Set o
       Ret : Op -> Set r

open Effect public

infixr 5 _⊕_
_⊕_
  : {ol or r : Level}
  → (effl : Effect {ol} {r})
  → (effr : Effect {or} {r})
  → Effect {(ol ⊔ or)} {r}
(effl ⊕ effr) .Op = Op effl ⊎ Op effr
(effl ⊕ effr) .Ret (inl op) = Ret effl op
(effl ⊕ effr) .Ret (inr op) = Ret effr op


FirstEffect = Effect {lsuc lzero} {lzero}
