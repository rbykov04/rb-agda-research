{-# OPTIONS --exact-split #-}
{-# OPTIONS  --backtracking-instance-search  #-}

module Effect.Core.Free where
open import Agda.Builtin.String
open import Agda.Builtin.Unit
open import Agda.Builtin.Maybe
open import Agda.Builtin.Nat
open import Agda.Builtin.Equality
open import Agda.Builtin.IO
open import Agda.Builtin.Unit
open import Agda.Builtin.String
open import Agda.Builtin.Sigma
open import Agda.Primitive

open import Mystdlib.Mystdlib
open import Mystdlib.IO

private
  variable
    a b c d e : Level
    A : Set a
    B : Set b
    C : Set c
    D : Set d
    E : Set e

record Effect : Set₁ where
 field Op  : Set
       Ret : Op -> Set

open Effect public

-- Free likes "engine" for callculation
data Free (eff : Effect) ( A : Set) : Set where
    pure   : A                                               -> Free eff A
    impure : (op : Op eff) -> (k : Ret eff op -> Free eff A) -> Free eff A

variable
    Eff  : Effect
    Eff1  : Effect
    Eff2  : Effect

coProduct : Effect -> Effect -> Effect
Op  (coProduct a b) = Sum (Op a)  (Op b)
Ret (coProduct a b) x = elim (Ret a) (Ret b) x

{-
-}



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
data EffectStorage  : Effect -> Effect -> Effect -> Set₁ where
    insert  : {Here There : Effect}
            -> EffectStorage (coProduct Here There) Here There
    sift    : {E Here Next There : Effect}
            -> EffectStorage E Here There
            -> EffectStorage (coProduct Next E) Here (coProduct Next There)

instance
  insert1 :
            {Here There : Effect}
            -> EffectStorage (coProduct Here There) Here There
  insert1 = insert

  sift1 :
        {E Here Next There : Effect}
        -> {{EffectStorage E Here There}}
        -> (EffectStorage (coProduct Next E) Here (coProduct Next There))
  sift1 ⦃ w ⦄ = sift w



--I need to rename this
inj-insert-left : {E Here There : Effect}
                  {{ w : EffectStorage E Here There }}
                  -> Op Here
                  -> Op E
inj-insert-left {{ insert }} op = injl op
inj-insert-left {{ sift w }} op = injr (inj-insert-left {{w}} op)

inj-insert-right : {E Here There : Effect} {{ w : EffectStorage E Here There }}  -> Op There -> Op E
inj-insert-right {{ insert }} op = injr op
inj-insert-right {{ w = sift w }} (injl next) = injl next
inj-insert-right {{ w = sift w }} (injr there) = injr (inj-insert-right {{w}} there)


--I need to rename this
proj-ret-left :
        {E Here There : Effect}
        -> {{ w : EffectStorage E Here There }}
        -> {op : Op Here}
        -> Ret E (inj-insert-left op)
        -> Ret Here op
proj-ret-left {{ insert }} x = x
proj-ret-left {{ sift w }} x = proj-ret-left {{w}} x


--I need to rename this
proj-ret-right :
        {E Here There : Effect}
        -> {{ w : EffectStorage E Here There }}
        -> {op : Op There}
        -> Ret E (inj-insert-right op)
        -> Ret There op
proj-ret-right {{ insert }} x =  x
proj-ret-right ⦃ w = sift w ⦄ {injl next } x = x
proj-ret-right ⦃ w = sift w ⦄ {injr op} x = proj-ret-right {{w}} x

injl-ret-eq :
        {E Here There : Effect}
        -> {{ w : EffectStorage E Here There }}
        -> (op : Op Here)
        -> Ret E (inj-insert-left op) ≡ Ret Here op
injl-ret-eq ⦃ insert ⦄ _ = refl
injl-ret-eq ⦃ sift w ⦄ = injl-ret-eq {{w}}

injr-ret-eq :
        {E Here There : Effect}
        -> {{ w : EffectStorage E Here There }}
        -> (op : Op There)
        -> Ret E (inj-insert-right op) ≡ Ret There op
injr-ret-eq ⦃ insert ⦄ _ = refl
injr-ret-eq ⦃ w = sift w ⦄ (injl x) = refl
injr-ret-eq ⦃ w = sift w ⦄ (injr y) = injr-ret-eq {{w}} y

case : {E Here There : Effect}
       -> {{ w : EffectStorage E Here There }}
        -> Op E
        -> (Op Here -> A )
        -> (Op There -> A )
        -> A
case {{ w = insert }} (injl here) fromHere fromThere = fromHere here
case {{ w = insert }} (injr there) fromHere fromThere = fromThere there
case {{ w = sift w }} (injl there) fromHere fromThere = fromThere (injl there)
case {{ w = sift w }} (injr e) fromHere fromThere = case {{w}} e fromHere λ there -> fromThere (injr there)
case-eq : {E Here There : Effect}
       -> {{ w : EffectStorage E Here There }}
        -> (op : Op E)
        -> ((op' : Op Here)  -> (op ≡ inj-insert-left  op') -> A)
        -> ((op' : Op There) -> (op ≡ inj-insert-right op') -> A)
        -> A
case-eq {{ w = insert }} (injl x) eq-here eq-there = eq-here  x refl
case-eq {{ w = insert }} (injr y) eq-here eq-there = eq-there y refl
case-eq {{ w = sift w }} (injl x) eq-here eq-there = eq-there (injl x) refl
case-eq {{ w = sift w }} (injr e) eq-here eq-there =
    case-eq {{w}} e
        (λ  here eq -> eq-here  here (cong injr eq))
        (λ there eq -> eq-there (injr there) (cong injr eq))



help : {E Here There : Effect}
       -> {{ w   : EffectStorage E Here There }}
       -> (  op' : Op Here)
       -> (  op  : Op E)
       -> (  eq  : op ≡ inj-insert-left op')
       -> Ret Here op'
       -> Ret E    op
help {E} {Here} ⦃ w ⦄ op' op eq = subst id (begin
        Ret Here op'
        ≡⟨ sym (injl-ret-eq {{w}} op')  ⟩
        Ret E (inj-insert-left op')
        ≡⟨ sym (cong (Ret E) eq)  ⟩
        Ret E op
        ∎)

help2 : {E Here There : Effect}
       -> {{ w   : EffectStorage E Here There }}
       -> (  op' : Op There)
       -> (  op  : Op E)
       -> (  eq  : op ≡ inj-insert-right op')
       -> Ret There op'
       -> Ret E    op
help2 {E} {Here} {There} ⦃ w ⦄ op' op eq = subst id (begin
        Ret There op'
        ≡⟨ sym (injr-ret-eq {{w}} op')  ⟩
        Ret E (inj-insert-right op')
        ≡⟨ sym (cong (Ret E) eq)  ⟩
        Ret E op
        ∎)

-- What doest it do?
-- How doest it do?
to-front : {E Here There : Effect}
          -> {A : Set}
          -> {{ w : EffectStorage E Here There }}
          -> Free E A
          -> Free (coProduct Here There) A
to-front ⦃ w = w ⦄ (pure x) = pure x
to-front ⦃ w = insert ⦄ (impure op k) = impure op
                            (λ x -> to-front {{insert}} (k x))
to-front ⦃ w = sift w ⦄ (impure (injl op) k) =
    impure (injr (injl op)) (λ x -> to-front {{sift w}} (k x))
to-front { Here = Here } {{ sift {E = E} {There = There} w }} (impure (injr op) k) = case-eq {{ w }} op
    (λ op' eq -> impure (injl op') λ x -> to-front {{sift w}} (k (help  {{w}} op' op eq x)))
    (λ op' eq -> impure (injr (injr op')) λ x -> to-front {{sift w}} (k (help2 {{w}} op' op eq x)))

{-
hello-throw1 : {E There1 There2 : Effect} {A : Set}
             -> {{EffectStorage E Output There1}}
             -> {{EffectStorage E Throw There2}}
             -> Free E A

hello-throw1 = do `out "Hello";
                    `out " ";
                    `out "world";
                    `throw
-}

record Handler (A : Set) (E : Effect) (P : Set) (B : Set) (Continue : Effect) : Set₁ where
    field ret : A -> P -> Free Continue B
          hdl : Alg E (P -> Free Continue B)
open Handler public

-- how does it work???
-- I understand (maybe) what it doest. but how??
givenHandle :
            {A B P : Set}
            -> {E Here There : Effect}
            -> {{ EffectStorage E Here There  }}
            -> Handler A Here P B There
            -> Free E A
            -> (P -> Free There B)
givenHandle {A} {B} {P} {E} {Here} {There} h eff =
    fold (ret h) func (to-front eff) where
    func : Alg (coProduct Here There) (P -> Free There B)
    func  (injl op) k p = hdl h op k p
    func (injr op) k p = impure op (λ x → k x p)

-- This is EFFECT MASKING
-- What is it?????
--
#_ : {Eff Eff0 Eff' : Effect}
     -> {{w : EffectStorage Eff Eff0 Eff'}}
     -> Free Eff' A
     -> Free Eff  A
#_ ⦃ w ⦄ = fold pure \ op' k → impure (inj-insert-right op')
                                      \ ret' → k (proj-ret-right {{w}} ret')

