{-# OPTIONS --exact-split #-}

open import Agda.Builtin.String using (String)
open import Agda.Builtin.Unit using (⊤)
-- also known as Either
data Sum (A : Set) (B : Set) : Set where
  injl : (x : A) → Sum A B
  injr : (y : B) → Sum A B

data ⊥ : Set where
⊥-elim : ∀ {w} {Whatever : Set w} → ⊥ → Whatever
⊥-elim ()


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

-- Free likes "engine" for callculation
data Free (eff : Effect) ( A : Set) : Set where
    pure   : A                                            -> Free eff A
    impure : (op : Op eff) (k : Ret eff op -> Free eff A) -> Free eff A

-- Let's try this in some practice

data OutOp : Set where
    out : String -> OutOp


Output : Effect
Op  Output = OutOp
Ret Output (out str) = ⊤



hello : Free Output ⊤
hello = impure (out "Hello") pure

helloWorld : Free Output ⊤
helloWorld = impure (out "Hello") (λ _ -> impure (out " World") pure)

data ThrowOp : Set where
    throw : ThrowOp

Throw : Effect
Op Throw = ThrowOp
Ret Throw throw = ⊥


coProduct : Effect -> Effect -> Effect
Op  (coProduct a b) = Sum (Op a)  (Op b)
Ret (coProduct a b) x = elim (Ret a) (Ret b) x

hello-throw : Free (coProduct Output Throw) A
hello-throw = impure (injl (out "Hello")) (λ _ -> impure (injr throw) ⊥-elim)


data Row    : Effect -> Effect -> Effect -> Set₁ where
    insert  : (a b : Effect)
            -> Row (coProduct a b) a b
    sift    : (a b c : Effect)
            -> Row a b c
            -> Row (coProduct a b) b (coProduct a c)
