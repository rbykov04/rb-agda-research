{-# OPTIONS --exact-split #-}
{-# OPTIONS  --backtracking-instance-search  #-}
module Effect.Core.Hefty where

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

open import Effect.Core.Free  hiding (_>>=_; _>>_)

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
          ForkH : OpH -> Effect -- FIXME Fork vs ForkH?
          RetH : OpH -> Set
open EffectH public

infixr 12 _+E+_
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

_>>_ : {H : EffectH} -> Hefty H A -> Hefty H B -> Hefty H B
a >> b = a >>= \ _ → b


{-
--Maybe:

data Storage (X : Set₁) (_OR_ : X -> X -> X) : X -> X -> X -> Set₁ where
    insert  : {x0 x' : X}      -> Storage X _OR_ (x0 OR x') x0 x'
    sift : {x x0 x1 x' : X} -> Storage X _OR_ x x0 x' -> Storage X _OR_ (x1 OR x) x0 (x1 OR x')

EffectHStorage : EffectH -> EffectH -> EffectH -> Set₁
EffectHStorage = Storage EffectH (_+E+_)
-}


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
inl-ret-== : {H H0 H' : EffectH}
           -> {{w : EffectHStorage H H0 H' }}
           -> (op : OpH H0)
           -> RetH H (inj-left op) ≡ RetH H0 op
inl-ret-== ⦃ w = insert ⦄ op = refl
inl-ret-== ⦃ w = sift w ⦄ op = inl-ret-== {{w}} op

inr-ret-== : {H H0 H' : EffectH}
           -> {{w : EffectHStorage H H0 H' }}
           -> (op : OpH H')
           -> RetH H (inj-right op) ≡ RetH H' op
inr-ret-== ⦃ w = insert ⦄ op = refl
inr-ret-== ⦃ w = sift w ⦄ (injl x) = refl
inr-ret-== ⦃ w = sift w ⦄ (injr op) = inr-ret-== {{w}} op


inl-fork-== : {H H0 H' : EffectH}
           -> {{w : EffectHStorage H H0 H' }}
           -> (op : OpH H0)
           -> ForkH H (inj-left op) ≡ ForkH H0 op
inl-fork-== ⦃ w = insert ⦄ op = refl
inl-fork-== ⦃ w = sift w ⦄ op = inl-fork-== {{w}} op

inr-fork-== : {H H0 H' : EffectH}
           -> {{w : EffectHStorage H H0 H' }}
           -> (op : OpH H')
           -> ForkH H (inj-right op) ≡ ForkH H' op
inr-fork-== ⦃ w = insert ⦄ op = refl
inr-fork-== ⦃ w = sift w ⦄ (injl x) = refl
inr-fork-== ⦃ w = sift w ⦄ (injr op) = inr-fork-== {{w}} op

-- OMG! what does it need for?
inl-prong-== : {H H0 H' : EffectH}
           -> {{w : EffectHStorage H H0 H' }}
           -> {op : OpH H0}
           -> (b  : Op (ForkH H (inj-left op)))
           -> Ret (ForkH H (inj-left op)) b ≡ Ret (ForkH H0 op) (subst Op (inl-fork-== {{w}} op) b)
inl-prong-== ⦃ w = insert ⦄ op = refl
inl-prong-== ⦃ w = sift w ⦄ op = inl-prong-== {{w}} op

inr-prong-== : {H H0 H' : EffectH}
           -> {{w : EffectHStorage H H0 H' }}
           -> (op : OpH H')
           -> (b  : Op (ForkH H (inj-right op)))
           -> Ret (ForkH H (inj-right op)) b ≡ Ret (ForkH H' op) (subst Op (inr-fork-== {{w}} op) b)
inr-prong-== ⦃ w = insert ⦄ op b = refl
inr-prong-== ⦃ w = sift w ⦄ (injl x) b = refl
inr-prong-== ⦃ w = sift w ⦄ (injr op) b = inr-prong-== {{w}} op b

inl-prong2-== : {H H0 H' : EffectH}
           -> {{w : EffectHStorage H H0 H' }}
           -> {op : OpH H0}
           -> (b  : Op (ForkH H0 op))
           -> Ret (ForkH H0 op) b ≡ Ret (ForkH H (inj-left op)) (subst Op (sym (inl-fork-== {{w}} op)) b)
inl-prong2-== ⦃ w = insert ⦄ b = refl
inl-prong2-== ⦃ w = sift w ⦄ b = inl-prong2-== {{w}}  b

inr-prong2-== : {H H0 H' : EffectH}
           -> {{w : EffectHStorage H H0 H' }}
           -> (op : OpH H')
           -> (b  : Op (ForkH H' op))
           -> Ret (ForkH H' op) b ≡ Ret (ForkH H (inj-right op)) (subst Op (sym (inr-fork-== {{w}} op)) b)
inr-prong2-== ⦃ w = insert ⦄ op b = refl
inr-prong2-== ⦃ w = sift w ⦄ (injl x) b = refl
inr-prong2-== ⦃ w = sift w ⦄ (injr op) b = inr-prong2-== {{w}} op b

proj-ret-l : {H H0 H' : EffectH}
             {{ w : EffectHStorage H H0 H' }}
             -> {op : OpH H0}
             -> RetH H (inj-left op)
             -> RetH H0 op
proj-ret-l ⦃ w = insert ⦄ x = x
proj-ret-l ⦃ w = sift w ⦄ x = proj-ret-l {{w}} x

proj-ret-r : {H H0 H' : EffectH}
             {{ w : EffectHStorage H H0 H' }}
             -> (op : OpH H')
             -> RetH H (inj-right op)
             -> RetH H' op
proj-ret-r ⦃ w = insert ⦄ op x = x
proj-ret-r ⦃ w = sift w ⦄ (injl op) x = x
proj-ret-r ⦃ w = sift w ⦄ (injr op) x = proj-ret-r {{w}} op x

proj-ret2-l : {H H0 H' : EffectH}
             {{ w : EffectHStorage H H0 H' }}
             -> (op : OpH H0)
             -> RetH H0 op
             -> RetH H (inj-left op)
proj-ret2-l ⦃ w = insert ⦄ op x = x
proj-ret2-l ⦃ w = sift w ⦄ op x = proj-ret2-l {{w}} op x

proj-ret2-r : {H H0 H' : EffectH}
             {{ w : EffectHStorage H H0 H' }}
             -> (op : OpH H')
             -> RetH H' op
             -> RetH H (inj-right op)
proj-ret2-r ⦃ w = insert ⦄ op x = x
proj-ret2-r ⦃ w = sift w ⦄ (injl op) x = x
proj-ret2-r ⦃ w = sift w ⦄ (injr op) x = proj-ret2-r {{w}} op x


proj-fork-l : {H H0 H' H'' : EffectH}
              {{ w : EffectHStorage H H0 H' }}
              (op : OpH H0)
              -> ((b : Op (ForkH H0 op))           -> Hefty H'' (Ret (ForkH H0 op) b))
              -> ((b : Op (ForkH H (inj-left op))) -> Hefty H'' (Ret (ForkH H (inj-left op)) b))
proj-fork-l {{ w }} op f b = let
                x = f (subst Op (inl-fork-== {{w}} op) b)
                in subst ((Hefty _)) (sym (inl-prong-== {{w}} b)) x

proj-fork-r : {H H0 H' H'' : EffectH}
              {{ w : EffectHStorage H H0 H' }}
              -> (op : OpH H')
              -> ((b : Op (ForkH H' op))            -> Hefty H'' (Ret (ForkH H' op) b))
              -> ((b : Op (ForkH H (inj-right op))) -> Hefty H'' (Ret (ForkH H (inj-right op)) b))
proj-fork-r {{ w }} op f b = let
                x = f (subst Op (inr-fork-== {{w}} op) b)
                in subst ((Hefty _)) (sym (inr-prong-== {{w}} op b)) x

proj-fork2-l : {H H0 H' H'' : EffectH}
              {{ w : EffectHStorage H H0 H' }}
              -> {op : OpH H0}
              -> ((b : Op (ForkH H (inj-left op))) -> Hefty H'' (Ret (ForkH H (inj-left op)) b))
              -> ((b : Op (ForkH H0 op))           -> Hefty H'' (Ret (ForkH H0 op) b))
proj-fork2-l {{ w }} {op} f b = let
                x = f (subst Op (sym (inl-fork-== {{w}} op)) b)
                in subst ((Hefty _)) (sym (inl-prong2-== {{w}} b)) x

proj-fork2-r : {H H0 H' H'' : EffectH}
              {{ w : EffectHStorage H H0 H' }}
              -> (op : OpH H')
              -> ((b : Op (ForkH H (inj-right op))) -> Hefty H'' (Ret (ForkH H (inj-right op)) b))
              -> ((b : Op (ForkH H' op))           -> Hefty H'' (Ret (ForkH H' op) b))
proj-fork2-r {{ w }} op f b = let
                x = f (subst Op (sym (inr-fork-== {{w}} op)) b)
                in subst ((Hefty _)) (sym (inr-prong2-== {{w}} op b)) x

case-h : {H H0 H' : EffectH}
         {{ w : EffectHStorage H H0 H' }}
         -> OpH H
         -> (OpH H0 -> A)
         -> (OpH H' -> A)
         -> A
case-h ⦃ w = insert ⦄ (injl x) f g = f x
case-h ⦃ w = insert ⦄ (injr y) f g = g y
case-h ⦃ w = sift w ⦄ (injl x) f g = g (injl x)
case-h ⦃ w = sift w ⦄ (injr y) f g = case-h {{w}} y f λ z → g (injr z)

case-h-== : {H H0 H' : EffectH}
            {{ w : EffectHStorage H H0 H' }}
            -> (op : OpH H)
            -> ((op' : OpH H0) -> (op ≡ inj-left op')  -> A)
            -> ((op' : OpH H') -> (op ≡ inj-right op') -> A)
            -> A
case-h-== ⦃ w = insert ⦄ (injl x) f g = f x refl
case-h-== ⦃ w = insert ⦄ (injr y) f g = g y refl
case-h-== ⦃ w = sift w ⦄ (injl x) f g = g (injl x) refl
case-h-== ⦃ w = sift w ⦄ (injr y) f g = case-h-==
              {{w}} y
              (λ op' x → f op' (cong injr x) )
              (λ op' x → g (injr op') (cong injr x))

{-

W
-- what does "D" stand for?
--              We can't use this type inside EffetcH. (OpH : Set)
--               |
data CatchOpD : Set₁ where
    catchD : Set -> CatchOpD


CatchD : EffectH
OpH   CatchD = {!CatchOpD!}
ForkH CatchD = {!!}
RetH  CatchD = {!!}

-}
record AlgH (H : EffectH) (F : Set -> Set) : Set₁ where
    field alg : (op   : OpH H)
                (fork : (s : Op (ForkH H op)) -> F (Ret (ForkH H op) s)) -- What is fork?
                (k    : RetH H op -> F A)                                -- What is k?
                -> F A
open AlgH public

variable
  m n : Level
  F F₀ F₁ F₂ F₃ : Set n → Set (n ⊔ m)  -- What is it???
  H0 H H' H'' H''' : EffectH


-- What does F mean??
foldH : (forall {A} -> A -> F A) -> AlgH H F -> Hefty H A -> F A
foldH g a (pure x) = g x
foldH g a (impure op f k) = alg a op (\ op → foldH g a (f op))
                                     (\ op → foldH g a (k op))
infixr 12 _+A+_
_+A+_ : {H1 H2 : EffectH} -> AlgH H1 F -> AlgH H2 F -> AlgH (H1 +E+ H2) F
alg (A1 +A+ A2) (injl x) fork k = alg A1 x fork k
alg (A1 +A+ A2) (injr y) fork k = alg A2 y fork k

Elaboration : EffectH -> Effect -> Set₁
Elaboration H Eff = AlgH H (Free Eff)


-- How does it work?
elaborate : {H : EffectH}{Eff : Effect} -> Elaboration H Eff -> Hefty H A -> Free Eff A
elaborate elab hefty = foldH pure elab hefty

