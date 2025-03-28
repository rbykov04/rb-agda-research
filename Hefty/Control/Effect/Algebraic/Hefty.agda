{-# OPTIONS --exact-split #-}
{-# OPTIONS  --backtracking-instance-search  #-}
module Control.Effect.Algebraic.Hefty
    where

open import Foundation.Base

open import Agda.Builtin.String
open import Agda.Builtin.Unit
open import Agda.Builtin.Bool
open import Agda.Builtin.List
open import Agda.Builtin.Nat
open import Agda.Builtin.Equality
open import Agda.Builtin.IO
open import Agda.Builtin.Unit
open import Agda.Builtin.String
open import Agda.Builtin.Sigma
open import Agda.Primitive

open import Mystdlib.Mystdlib

open import Control.Effect.Algebraic.Effect
open import Control.Effect.Algebraic.Effect.Free hiding (_>>_ ; _>>=_ ; fold)

private
  variable
    a b c d e : Level
    A : Set a
    B : Set b
    C : Set c
    D : Set d
    E : Set e

record Effectᴴ {o k r : Level} : Set (lsuc (o ⊔ k ⊔ r)) where
    field Opᴴ  : Set o
          Fork : Opᴴ -> Effect {k} {r}
          Retᴴ : Opᴴ -> Set r
open Effectᴴ public

infixr 12 _⊕ᴴ_
_⊕ᴴ_
  : {ol or k r : Level}
  -> Effectᴴ {ol} {k} {r}
  -> Effectᴴ {or} {k} {r}
  -> Effectᴴ {ol ⊔ or} {k} {r}
(effl ⊕ᴴ effr) .Opᴴ = Opᴴ effl ⊎ Opᴴ effr
(effl ⊕ᴴ effr) .Fork (inl op) = Fork effl op
(effl ⊕ᴴ effr) .Fork (inr op) = Fork effr op
(effl ⊕ᴴ effr) .Retᴴ (inl op) = Retᴴ effl op
(effl ⊕ᴴ effr) .Retᴴ (inr op) = Retᴴ effr op



data Hefty {o k r a : Level}(H : Effectᴴ {o} {k} {r}) (A : Set a) : Set (o ⊔ k ⊔ r ⊔ a) where
    pure   : A -> Hefty H A
    impure : (op  : Opᴴ H)
             -> (f   : (a : Op (Fork H op)) -> Hefty H (Ret (Fork H op) a))
             -> (k : Retᴴ H op -> Hefty H A)
             -> Hefty H A

open Hefty public

private
  variable
    o k r : Level
    H Row Compl : Effectᴴ {o} {k} {r}
    X Y Z Y\X : Effectᴴ {o} {k} {r}



_>>=_ : Hefty H A -> (A -> Hefty H B) -> Hefty H B
pure x        >>= g = g x
impure op f k >>= g = impure op f \ x → k x >>= g

_>>_ : Hefty H A -> Hefty H B -> Hefty H B
a >> b = a >>= \ _ → b

record Algᴴ {o k r : Level} (H : Effectᴴ {o} {k} {r}) (G : Set r -> Set k) : Set (lsuc (o ⊔ k ⊔ r))
    where
    field alg : (op   : Opᴴ H)
                (fork : (s : Op (Fork H op)) -> G (Ret (Fork H op) s))
                (k    : Retᴴ H op -> G A)
                -> G A
open Algᴴ public

fold :
    {o k r : Level}
    -> {H : Effectᴴ {o} {k} {r}}
    -> {A : Set r}
    -> {F : Set r -> Set k}
    -> (forall {A} -> A -> F A)
    -> Algᴴ H F -> Hefty H A
    -> F A
fold g a (pure x) = g x
fold g a (impure op f k) = alg a op (\ op → fold g a (f op))
                                     (\ op → fold g a (k op))


infixr 12 _⊕ᴬ_
_⊕ᴬ_
    : {o k r : Level}
    -> {H1 H2 : Effectᴴ {o} {k} {r}}
    -> {F : Set r -> Set k}
    -> Algᴴ H1 F -> Algᴴ H2 F -> Algᴴ (H1 ⊕ᴴ H2) F
(A1 ⊕ᴬ A2) .alg (inl x) fork k = alg A1 x fork k
(A1 ⊕ᴬ A2) .alg (inr y) fork k = alg A2 y fork k


Elaboration
    : {o r : Level}
    -> Effectᴴ {o} {o ⊔ r} {r}   -- Smt is wrong here
    -> Effect {o} {r}
    -> Set (lsuc o ⊔ lsuc r ⊔ lsuc (o ⊔ r))
Elaboration H Eff = Algᴴ H (Free Eff)


elaborate
    : {o r : Level}
    -> {A : Set r}
    -> {H : Effectᴴ {o} {o ⊔ r} {r}}   -- Smt is wrong here
    -> {Eff : Effect {o} {r}}
    -> Elaboration H Eff
    -> Hefty H A
    -> Free Eff A
elaborate elab hefty = fold pure elab hefty

record Elab
        {o r : Level}
        (H : Effectᴴ {o} {o ⊔ r} {r})
        (Eff : Effect {o} {r})
    : Set (lsuc o ⊔ lsuc r ⊔ lsuc (o ⊔ r))
    where
    field orate : Algᴴ H (Free Eff)

open Elab public

elab
    : {o r : Level}
    -> {A : Set r}
    -> {H : Effectᴴ {o} {o ⊔ r} {r}}
    -> {Eff : Effect {o} {r}}
    -> Elab H Eff -> Hefty H A ->  Free Eff A
elab x h = elaborate (orate x) h

instance
    auto-elab
        :  {o r   : Level}
        -> {H1 H2 : Effectᴴ {o} {o ⊔ r} {r}}
        -> {E     : Effect {o} {r}}
        -> {{ E1 : Elab H1 E }}
        -> {{ E2 : Elab H2 E }}
        -> Elab ( H1 ⊕ᴴ H2 ) E
    auto-elab ⦃ e1 ⦄ ⦃ e2 ⦄ .orate = orate e1 ⊕ᴬ orate e2
