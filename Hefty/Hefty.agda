module Hefty where

open import Agda.Builtin.String
open import Agda.Builtin.Unit
open import Agda.Builtin.Nat
open import Agda.Builtin.Equality
open import Agda.Builtin.IO
open import Agda.Builtin.Unit
open import Agda.Builtin.String
open import Agda.Builtin.Sigma
open import Agda.Primitive

open import Free hiding (_>>=_)

private
  variable
    a b c d e : Level
    A : Set a
    B : Set b
    C : Set c
    D : Set d
    E : Set e



record EffectH : Set₁ where
    field OpH  : Set
          ForkH : OpH -> Effect
          RetH : OpH -> Set
open EffectH

_+E+_ : EffectH -> EffectH -> EffectH
OpH   (a +E+ b) = Sum (OpH a) (OpH b)
ForkH (a +E+ b) = elim (ForkH a) (ForkH b)
RetH  (a +E+ b) = elim (RetH a)  (RetH b)

data Hefty (H : EffectH) (A : Set) : Set where
    pure   : A -> Hefty H A
    impure : (op  : OpH H)
             -> (f   : (a : Op (ForkH H op)) -> Hefty H (Ret (ForkH H op) a))
             -> (k : RetH H op -> Hefty H A)
             -> Hefty H A

open Hefty public

data CensorOp : Set where
    censor : (String -> String) -> CensorOp

Censor : EffectH
OpH  Censor = CensorOp
ForkH Censor (censor str) = record { Op = ⊤ ; Ret = \ _ → ⊤ }
RetH Censor (censor str) = ⊤

-- what is it?
censorOP : {H : EffectH} -> (String -> String) -> Hefty (Censor +E+ H) ⊤ -> Hefty (Censor +E+ H) ⊤
censorOP f m = impure (injl (censor f)) (\ _ → m) pure

censor1 : {H : EffectH} -> Hefty Censor Nat
censor1  = impure (censor (\ s → s ++ ".")) pure \ _ → pure zero

-- I don't understand it
_>>=_ : {H : EffectH} -> Hefty H A -> (A -> Hefty H B) -> Hefty H B
pure x        >>= g = g x
impure op f k >>= g = impure op f \ x → k x >>= g

data EffectHStorage : EffectH -> EffectH -> EffectH → Set₁ where
  insert  : {H0 H' : EffectH} -> EffectHStorage (H0 +E+ H') H0 H'
  sift    : {H H0 H1 H' : EffectH}
          -> EffectHStorage H H0 H'
          -> EffectHStorage (H1 +E+ H) H0 (H1 +E+ H')

instance
  insert-h :
            {H0 H' : EffectH}
            -> EffectHStorage (H0 +E+ H') H0 H'
  insert-h = insert

  sift-h :
        {H H0 H1 H' : EffectH}
        -> {{EffectHStorage H H0 H'}}
        -> (EffectHStorage (H1 +E+ H) H0 (H1 +E+ H'))
  sift-h ⦃ w ⦄ = sift w


--I need to rename this
inj-left : {H H0 H' : EffectH}
           {{ w : EffectHStorage H H0 H' }}
           -> OpH H0
           -> OpH H
inj-left ⦃ insert ⦄ = injl
inj-left ⦃ sift p ⦄ = \ x → injr (inj-left {{p}} x)

inj-right : {H H0 H' : EffectH}
           -> {{ EffectHStorage H H0 H' }}
           -> OpH H'
           -> OpH H
inj-right ⦃ insert ⦄ = \ x → injr x
inj-right {H' = _} ⦃ sift w ⦄ (injl x) = injl x
inj-right {H' = _} ⦃ sift w ⦄ (injr y) = injr (inj-right {{w}} y)

-- so many hard work
injl-ret-eq-h : {H H0 H' : EffectH}
           -> {{w : EffectHStorage H H0 H' }}
           -> (op : OpH H0)
           -> RetH H (inj-left op) ≡ RetH H0 op
injl-ret-eq-h ⦃ w = insert ⦄ op = refl
injl-ret-eq-h ⦃ w = sift w ⦄ op = injl-ret-eq-h {{w}} op



Lift : Effect -> EffectH
OpH   (Lift x)   = Op x
ForkH (Lift x) _ = Nil
RetH  (Lift x)   = Ret x
{-
up : {E : Effect}
     -> {H H' : EffectH}
     -> {{ w : EffectHStorage H (Lift E) H' }}
     -> (op : Op E)
     -> Hefty H (Ret E op)

up {{w}} op = impure {!!} {!!} {!!}
 impure
 (inj▹ₗ ⦃ w ⦄ op)
 (proj-fork▹ₗ ⦃ w ⦄ (λ b → ⊥-elim b))
 (pure ∘ proj-ret▹ₗ ⦃ w ⦄)
-}
