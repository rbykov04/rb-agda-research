{-# OPTIONS --exact-split #-}
{-# OPTIONS  --backtracking-instance-search  #-}
module Control.Effect.Algebraic.Hefty.RowInsert
    where

open import Agda.Builtin.Equality
open import Foundation.Base

open import Control.Effect.Algebraic.Hefty
open import Control.Effect.Algebraic.Effect

private
  variable
    a o k r : Level
    A : Set a
    H H0 H' H'' Row Compl : Effectᴴ {o} {k} {r}
    X Y Z Y\X : Effectᴴ {o} {k} {r}

data EffectHStorage {o k r : Level}
    : Effectᴴ {o} {k} {r}
    -> Effectᴴ {o} {k} {r}
    -> Effectᴴ {o} {k} {r}
    -> Set (lsuc (o ⊔ k ⊔ r))
    where
  insert  : {X Y : Effectᴴ {o} {k} {r}}
            -> EffectHStorage (X ⊕ᴴ Y) X Y
  sift    : {X Y Z Y\X : Effectᴴ {o} {k} {r}}
          -> EffectHStorage Y X Y\X
          -> EffectHStorage (Z ⊕ᴴ Y) X (Z ⊕ᴴ Y\X)


heftyrow_＝_∣_ : (Row E Compl : Effectᴴ {o} {k} {r}) -> Set (lsuc (o ⊔ k ⊔ r))
heftyrow Row ＝ E ∣ Compl = EffectHStorage Row E Compl


instance
  insert-h : EffectHStorage (X ⊕ᴴ Y) X Y
  insert-h = insert

  sift-h : {X Y Z Y\X : Effectᴴ {o} {k} {r}}
         -> {{EffectHStorage {o} {k} {r} Y X Y\X}}
         -> EffectHStorage {o} {k} {r} (Z ⊕ᴴ Y) X (Z ⊕ᴴ Y\X)
  sift-h ⦃ w ⦄ = sift w


inject : {{ heftyrow Y ＝ X ∣ Y\X }} -> Opᴴ X -> Opᴴ Y
inject ⦃ insert ⦄ = inl
inject ⦃ sift p ⦄ x = inr (inject {{p}} x)

project-ret
    : {{ w : heftyrow Y ＝ X ∣ Y\X }}
    -> {op : Opᴴ X} -> Retᴴ Y (inject {{w}} op) -> Retᴴ X op
project-ret ⦃ w = insert ⦄ x = x
project-ret ⦃ w = sift w ⦄ x = project-ret {{w}} x


inject-right
    : {{ w : heftyrow H ＝ H0 ∣ H' }}
    -> Opᴴ H'
    -> Opᴴ H
inject-right ⦃ insert ⦄ = \ x → inr x
inject-right {H' = _} ⦃ sift w ⦄ (inl x) = inl x
inject-right {H' = _} ⦃ sift w ⦄ (inr y) = inr (inject-right {{w}} y)

inr-ret-==
    : {{ w : heftyrow H ＝ H0 ∣ H' }}
    -> (op : Opᴴ H')
    -> Retᴴ H (inject-right op) ≡ Retᴴ H' op
inr-ret-== ⦃ w = insert ⦄ op = refl
inr-ret-== ⦃ w = sift w ⦄ (inl x) = refl
inr-ret-== ⦃ w = sift w ⦄ (inr op) = inr-ret-== {{w}} op


inl-fork-==
    : {{ w : heftyrow H ＝ H0 ∣ H' }}
    -> (op : Opᴴ H0)
    -> Fork H (inject {{w}} op) ≡ Fork H0 op
inl-fork-== ⦃ w = insert ⦄ op = refl
inl-fork-== ⦃ w = sift w ⦄ op = inl-fork-== {{w}} op

inr-fork-==
    : {{ w : heftyrow H ＝ H0 ∣ H' }}
    -> (op : Opᴴ H')
    -> Fork H (inject-right {{w}} op) ≡ Fork H' op
inr-fork-== ⦃ w = insert ⦄ op = refl
inr-fork-== ⦃ w = sift w ⦄ (inl x) = refl
inr-fork-== ⦃ w = sift w ⦄ (inr op) = inr-fork-== {{w}} op

inl-prong-==
    : {{ w : heftyrow H ＝ H0 ∣ H' }}
    -> {op : Opᴴ H0}
    -> (b  : Op (Fork H (inject {{w}} op)))
    -> Ret (Fork H (inject {{w}} op)) b
       ≡ Ret (Fork H0 op)
       (subst2 Op (inl-fork-== {{w}} op) b)
inl-prong-== ⦃ w = insert ⦄ op = refl
inl-prong-== ⦃ w = sift w ⦄ op = inl-prong-== {{w}} op

inr-prong-==
    : {{ w : heftyrow H ＝ H0 ∣ H' }}
    -> (op : Opᴴ H')
    -> (b  : Op (Fork H (inject-right {{w}} op)))
    -> Ret (Fork H (inject-right {{w}} op)) b
       ≡ Ret (Fork H' op) (subst2 Op (inr-fork-== {{w}} op) b)
inr-prong-== ⦃ w = insert ⦄ op b = refl
inr-prong-== ⦃ w = sift w ⦄ (inl x) b = refl
inr-prong-== ⦃ w = sift w ⦄ (inr op) b = inr-prong-== {{w}} op b

inl-prong2-==
    : {{ w : heftyrow H ＝ H0 ∣ H' }}
    -> {op : Opᴴ H0}
    -> (b  : Op (Fork H0 op))
    -> Ret (Fork H0 op) b ≡ Ret (Fork H (inject {{w}} op)) (subst2 Op (sym (inl-fork-== {{w}} op)) b)
inl-prong2-== ⦃ w = insert ⦄ b = refl
inl-prong2-== ⦃ w = sift w ⦄ b = inl-prong2-== {{w}}  b

inr-prong2-==
    : {{ w : heftyrow H ＝ H0 ∣ H' }}
    -> (op : Opᴴ H')
    -> (b  : Op (Fork H' op))
    -> Ret (Fork H' op) b ≡ Ret (Fork H (inject-right {{w}} op)) (subst2 Op (sym (inr-fork-== {{w}} op)) b)
inr-prong2-== ⦃ w = insert ⦄ op b = refl
inr-prong2-== ⦃ w = sift w ⦄ (inl x) b = refl
inr-prong2-== ⦃ w = sift w ⦄ (inr op) b = inr-prong2-== {{w}} op b

proj-ret-l
    : {{ w : heftyrow H ＝ H0 ∣ H' }}
    -> {op : Opᴴ H0}
    -> Retᴴ H (inject {{w}} op)
    -> Retᴴ H0 op
proj-ret-l ⦃ w = insert ⦄ x = x
proj-ret-l ⦃ w = sift w ⦄ x = proj-ret-l {{w}} x

proj-ret-r
    : {{ w : heftyrow H ＝ H0 ∣ H' }}
    -> (op : Opᴴ H')
    -> Retᴴ H (inject-right op)
    -> Retᴴ H' op
proj-ret-r ⦃ w = insert ⦄ op x = x
proj-ret-r ⦃ w = sift w ⦄ (inl op) x = x
proj-ret-r ⦃ w = sift w ⦄ (inr op) x = proj-ret-r {{w}} op x
proj-ret2-l
    : {{ w : heftyrow H ＝ H0 ∣ H' }}
    -> (op : Opᴴ H0)
    -> Retᴴ H0 op
    -> Retᴴ H (inject {{w}} op)
proj-ret2-l ⦃ w = insert ⦄ op x = x
proj-ret2-l ⦃ w = sift w ⦄ op x = proj-ret2-l {{w}} op x

proj-ret2-r
    : {{ w : heftyrow H ＝ H0 ∣ H' }}
    -> (op : Opᴴ H')
    -> Retᴴ H' op
    -> Retᴴ H (inject-right {{w}} op)
proj-ret2-r ⦃ w = insert ⦄ op x = x
proj-ret2-r ⦃ w = sift w ⦄ (inl op) x = x
proj-ret2-r ⦃ w = sift w ⦄ (inr op) x = proj-ret2-r {{w}} op x


proj-fork-l
    : {{ w : heftyrow H ＝ H0 ∣ H' }}
    (op : Opᴴ H0)
    -> ((b : Op (Fork H0 op)) -> Hefty H'' (Ret (Fork H0 op) b))
    -> ((b : Op (Fork H (inject {{w}} op))) -> Hefty H'' (Ret (Fork H (inject {{w}} op)) b))
proj-fork-l {{ w }} op f b = let
                x = f (subst2 Op (inl-fork-== {{w}} op) b)
                in subst2 ((Hefty _)) (sym (inl-prong-== {{w}} b)) x

proj-fork-r
    : {{ w : heftyrow H ＝ H0 ∣ H' }}
    -> (op : Opᴴ H')
    -> ((b : Op (Fork H' op))            -> Hefty H'' (Ret (Fork H' op) b))
    -> ((b : Op (Fork H (inject-right {{w}} op))) -> Hefty H'' (Ret (Fork H (inject-right {{w}} op)) b))
proj-fork-r {{ w }} op f b = let
                x = f (subst2 Op (inr-fork-== {{w}} op) b)
                in subst2 ((Hefty _)) (sym (inr-prong-== {{w}} op b)) x

proj-fork2-l
    : {{ w : heftyrow H ＝ H0 ∣ H' }}
    -> {op : Opᴴ H0}
    -> ((b : Op (Fork H (inject {{w}} op))) -> Hefty H'' (Ret (Fork H (inject {{w}} op)) b))
    -> ((b : Op (Fork H0 op))           -> Hefty H'' (Ret (Fork H0 op) b))
proj-fork2-l {{ w }} {op} f b = let
                x = f (subst2 Op (sym (inl-fork-== {{w}} op)) b)
                in subst2 ((Hefty _)) (sym (inl-prong2-== {{w}} b)) x

proj-fork2-r
    : {{ w : heftyrow H ＝ H0 ∣ H' }}
    -> (op : Opᴴ H')
    -> ((b : Op (Fork H (inject-right {{w}} op))) -> Hefty H'' (Ret (Fork H (inject-right {{w}} op)) b))
    -> ((b : Op (Fork H' op))           -> Hefty H'' (Ret (Fork H' op) b))
proj-fork2-r {{ w }} op f b = let
                x = f (subst2 Op (sym (inr-fork-== {{w}} op)) b)
                in subst2 ((Hefty _)) (sym (inr-prong2-== {{w}} op b)) x

case-h
    : {{ w : heftyrow H ＝ H0 ∣ H' }}
    -> Opᴴ H
    -> (Opᴴ H0 -> A)
    -> (Opᴴ H' -> A)
    -> A
case-h ⦃ w = insert ⦄ (inl x) f g = f x
case-h ⦃ w = insert ⦄ (inr y) f g = g y
case-h ⦃ w = sift w ⦄ (inl x) f g = g (inl x)
case-h ⦃ w = sift w ⦄ (inr y) f g = case-h {{w}} y f λ z → g (inr z)

case-h-==
    : {{ w : heftyrow H ＝ H0 ∣ H' }}
    -> (op : Opᴴ H)
    -> ((op' : Opᴴ H0) -> (op ≡ inject {{w}} op')  -> A)
    -> ((op' : Opᴴ H') -> (op ≡ inject-right {{w}} op') -> A)
    -> A
case-h-== ⦃ w = insert ⦄ (inl x) f g = f x refl
case-h-== ⦃ w = insert ⦄ (inr y) f g = g y refl
case-h-== ⦃ w = sift w ⦄ (inl x) f g = g (inl x) refl
case-h-== ⦃ w = sift w ⦄ (inr y) f g = case-h-==
              {{w}} y
              (λ op' x → f op' (cong inr x) )
              (λ op' x → g (inr op') (cong inr x))

{-
sendᴴ : {a b : Level} {E Here There : Effectᴴ {a} {b}}
     -> {{ w : EffectHStorage E Here There }}
     -> (op : Opᴴ Here)
     -> Hefty E (Retᴴ Here op)
sendᴴ {{w}} op =
    impure (inject {{w}} op)
            (proj-fork-l {{w}} op λ b₁ → {!!})
            (\ ret -> pure (project-ret {{w}} ret))

up
    : {{ w : heftyrow H ＝ (Lift E) ∣ H' }}
    -> (op : Op E)
    -> Hefty H (Ret E op)
up {{w}} op = impure (inject {{w}} op)
                     (proj-fork-l {{w}} op (λ ()))
                     \ x → pure (project-ret {{w}} x)


-}
