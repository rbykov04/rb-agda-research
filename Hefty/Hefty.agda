module Hefty where

open import Agda.Builtin.String
open import Agda.Builtin.Unit
open import Agda.Builtin.List
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


data ListSt : List Nat -> Nat -> List Nat  -> Set where
    here  : {x0 : Nat} {x' : List Nat}      -> ListSt (x0 ∷ x') x0 x'
    there : {x0 x1 : Nat} {x x' : List Nat} -> ListSt x x0 x' -> ListSt (x1 ∷ x) x0 (x1 ∷ x')

ll : ListSt (0 ∷ []) 0 []
ll = here

l2 : ListSt (zero ∷ zero ∷ []) 0 (zero ∷ [])
l2 = there here

l3 : ListSt (zero ∷ zero ∷ 5 ∷ []) 5 (zero ∷ zero ∷ [])
l3 = there (there here)

l4 : ListSt (zero ∷ zero ∷ zero ∷ 5 ∷ []) 5 (zero ∷ zero ∷ zero ∷ [])
l4 = there (there (there here))

l5 : ListSt (60 ∷ 10 ∷ 20 ∷ 5 ∷ []) 5 (60 ∷ 10 ∷ 20 ∷ [])
l5 = there (there (there here))



Lift : Effect -> EffectH
OpH   (Lift x)   = Op x
ForkH (Lift x) _ = Nil
RetH  (Lift x)   = Ret x

NilH : EffectH
NilH = Lift Nil

OutH : EffectH
OutH = Lift Output

storage1 : EffectHStorage (Lift Nil +E+ Lift Nil) NilH NilH
storage1 = insert

storage2 : EffectHStorage (OutH +E+ (OutH +E+ NilH)) OutH ((OutH +E+ NilH))
storage2 = sift insert

storage3 : EffectHStorage (NilH +E+ (OutH +E+ NilH))
                                     OutH
                          (NilH +E+ NilH)
storage3 = sift insert

storage4 : EffectHStorage  (OutH +E+ (NilH +E+ (OutH +E+ NilH)))
                                                OutH
                           (OutH +E+ (NilH +E+ NilH))
storage4 = sift (sift insert)


storage5 : EffectHStorage  (NilH +E+ (OutH +E+ (NilH +E+ (OutH +E+ NilH))))
                                                OutH
                           (NilH +E+ (OutH +E+ (NilH +E+ NilH)))
storage5 = sift (sift (sift insert))


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
