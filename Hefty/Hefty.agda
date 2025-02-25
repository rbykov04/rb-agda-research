{-# OPTIONS --exact-split #-}

-- also known as Either
data Sum (A : Set) (B : Set) : Set where
  injl : (x : A) → Sum A B
  injr : (y : B) → Sum A B


private
  variable
    A : Set
    B : Set
    C : Set


elim : forall
        {C : Sum A B → Set₁} →    -- it is a box
        ((x : A) → C (injl x)) → -- it is a function to convert left case to box
        ((x : B) → C (injr x)) → -- it is a function to convert right case to box
        (x : Sum A  B)             -- it is a what we can move to box
        → C x                     -- result
elim f g (injl x) = f x
elim f g (injr y) = g y



record Effect : Set₁ where
 field Op  : Set
       Ret : Op -> Set

open Effect


coProduct : Effect -> Effect -> Effect
Op  (coProduct a b) = Sum (Op a)  (Op b)
Ret (coProduct a b) x = elim (Ret a) (Ret b) x

-- Q1: how can we put into Effect????
