{-# OPTIONS --exact-split #-}

open import Agda.Builtin.String using (String)
open import Agda.Builtin.Unit
open import Agda.Builtin.Nat
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
    pure   : A                                               -> Free eff A
    impure : (op : Op eff) -> (k : Ret eff op -> Free eff A) -> Free eff A

variable
    Eff  : Effect
    Eff1  : Effect
    Eff2  : Effect

data OutOp : Set where
    out : String -> OutOp


Output : Effect
Op  Output = OutOp
Ret Output (out str) = ⊤


testOut : OutOp
testOut = out "aa"

hello0 : Free Output ⊤
hello0 = pure tt

hello2 : Free Output Nat
hello2 = pure 1

hello4 : Free Output ⊤
hello4 = impure (out "Hello") pure

helloWorld : Free Output ⊤
helloWorld = impure (out "Hello") (λ _ -> impure (out " World") pure)


data ClickOp : Set where
    click : Nat -> ClickOp
    clack : Nat -> ClickOp

Clicker : Effect
Op Clicker = ClickOp
Ret Clicker (click x) = Nat
Ret Clicker (clack x) = String


tick : Free Clicker Nat
tick = impure (click 1) λ x -> impure (click x) pure


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



-- How does it work?
Alg : (Eff : Effect) -> (A : Set) -> Set
Alg Eff A = (op : Op Eff)(k : Ret Eff op -> A ) -> A

fold : (A -> B)
        -> Alg Eff B
        -> Free Eff A
        -> B
fold g alg (pure x) = g x
fold g alg (impure op k) = alg op λ x -> fold g alg (k x)


-- How does it work?
_>>=_ : Free Eff A -> (A -> Free Eff B) -> Free Eff B
m >>= g = fold g impure m

-- How does it work?
_>>_ : Free Eff A → Free Eff B → Free Eff B
m1 >> m2 = m1 >>= λ _ → m2


--How does it use?
data EffectInRow  : Effect -> Effect -> Effect -> Set₁ where
    insert  : {Here There : Effect}
            -> EffectInRow (coProduct Here There) Here There
    sift    : {E Here Next There : Effect}
            -> EffectInRow E Here There
            -> EffectInRow (coProduct Next E) Here (coProduct Next There)

--I need to rename this
inj-insert-left : {E Here There : Effect} {{ w : EffectInRow E Here There }}  -> Op Here -> Op E
inj-insert-left {{ insert }} op = injl op
inj-insert-left {{ sift w }} op = injr (inj-insert-left {{w}} op)

inj-insert-right : {E Here There : Effect} {{ w : EffectInRow E Here There }}  -> Op There -> Op E
inj-insert-right {{ insert }} op = injr op
inj-insert-right {{ w = sift w }} (injl next) = injl next
inj-insert-right {{ w = sift w }} (injr there) = injr (inj-insert-right {{w}} there)


--I need to rename this
proj-ret-left :
        {E Here There : Effect}
        -> {{ w : EffectInRow E Here There }}
        -> {op : Op Here}
        -> Ret E (inj-insert-left op)
        -> Ret Here op
proj-ret-left {{ insert }} x = x
proj-ret-left {{ sift w }} x = proj-ret-left {{w}} x


--I need to rename this
proj-ret-right :
        {E Here There : Effect}
        -> {{ w : EffectInRow E Here There }}
        -> {op : Op There}
        -> Ret E (inj-insert-right op)
        -> Ret There op
proj-ret-right {{ insert }} x =  x
proj-ret-right ⦃ w = sift w ⦄ {injl next } x = x
proj-ret-right ⦃ w = sift w ⦄ {injr op} x = proj-ret-right {{w}} x

`out : {E There : Effect}
     -> {{ EffectInRow E Output There }}
     -> String
     -> Free E ⊤
`out {{ w }} str = impure (inj-insert-left (out str)) λ x -> pure ((proj-ret-left {{w}} x))

--Rethink this
`throw : {E There : Effect}
     -> {{ EffectInRow E Throw There }}
     -> Free E A
`throw {{ w }} = impure (inj-insert-left throw ) (λ x -> ⊥-elim (proj-ret-left {{w}} x))


hello-throw1 : {E There1 There2 : Effect} {A : Set}
             -> {{EffectInRow E Output There1}}
             -> {{EffectInRow E Throw There2}}
             -> Free E A
hello-throw1 = do `out "Hello";
                    `out " ";
                    `out "world";
                    `throw
