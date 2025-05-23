{-# OPTIONS  --backtracking-instance-search  #-}
module Effect.Core.Free2 where

open import Agda.Builtin.Unit
open import Agda.Builtin.Sigma
open import Agda.Builtin.List
open import Agda.Builtin.Char
open import Agda.Builtin.String
open import Agda.Builtin.IO
open import Agda.Builtin.Equality
open import Agda.Primitive

open import Mystdlib.Mystdlib


private
  variable
    a b c d e : Level
    A : Set a
    B : Set b
    C : Set c
    D : Set d
    E : Set e

record Effect2 {a b : Level} : Set (lsuc (a ⊔ b)) where -- (a ⊔ b) where
 constructor _⦊_
 field Op  : Set a
       Ret : Op -> Set b
open Effect2 public
infix 6 _⦊_

data Free2 {a b : Level} (eff : Effect2 {a} {b}) ( A : Set b) : Set (lsuc (a ⊔ b)) where
    pure   : A                                                -> Free2 eff A
    impure : (op : Op eff) -> (k : Ret eff op -> Free2 eff A) -> Free2 eff A



data Sum2 {a : Level} (A : Set a) (B : Set a) : Set ((a)) where
  injl : (x : A) → Sum2 A B
  injr : (y : B) → Sum2 A B

elim2 :
        {a : Level}
        {C : Sum2 A B → Set (lsuc a)} →    -- it is a box
        ((x : A) → C (injl x)) → -- it is a function to convert left case to box
        ((x : B) → C (injr x)) → -- it is a function to convert right case to box
        (x : Sum2 A  B)             -- it is a what we can move to box
        → C x                     -- result
elim2 f g (injl x) = f x
elim2 f g (injr y) = g y


coProduct2 : {a b : Level} -> Effect2 {a} {b} -> Effect2 {a} {b} -> Effect2 {a} {b}
coProduct2 {a} {b} x y .Op = Sum2 {a} (Op x) (Op y)
coProduct2 {a} {b} x y .Ret (injl x1) = Ret x x1
coProduct2 {a} {b} x y .Ret (injr y1) = Ret y y1

infixr 12 _|2>_
_|2>_ : {a b : Level} -> Effect2 {a} {b} -> Effect2 {a} {b} -> Effect2 {a} {b}
_|2>_ = coProduct2


--How does it use?
data EffectStorage2 {a b : Level} :
                       Effect2 {a} {b}
                    -> Effect2 {a} {b}
                    -> Effect2 {a} {b}
                    -> Set (lsuc (a ⊔ b))
                    where
    insert  : {Here There : Effect2 {a} {b}}
            -> EffectStorage2 {a} {b} (coProduct2 Here There) Here There
    sift  : {E Here Next There : Effect2 {a} {b}}
            -> EffectStorage2 {a} {b} E Here There
            -> EffectStorage2 {a} {b} (coProduct2 Next E) Here (coProduct2 Next There)
open EffectStorage2

instance
  insert21 : {a b : Level}
            -> {Here There : Effect2 {a} {b}}
            -> EffectStorage2 {a} {b} (coProduct2 Here There) Here There
  insert21 = insert

  sift21 : {a b : Level}
          {E Here Next There : Effect2 {a} {b}}
        -> {{EffectStorage2 E Here There}}
        -> (EffectStorage2 (coProduct2 Next E) Here (coProduct2 Next There))
  sift21 ⦃ w ⦄ = sift w



--I need to rename this
inj-insert-left2 : {a b : Level} {E Here There : Effect2 {a} {b}}
                  {{ w : EffectStorage2 E Here There }}
                  -> Op Here
                  -> Op E
inj-insert-left2 {{ insert }} op = injl op
inj-insert-left2 {{ sift w }} op = injr (inj-insert-left2 {{w}} op)

inj-insert-right2 :  {a b : Level} {E Here There : Effect2 {a} {b}} {{ w : EffectStorage2 E Here There }}  -> Op There -> Op E
inj-insert-right2 {{ insert }} op = injr op
inj-insert-right2 {{ w = sift w }} (injl next) = injl next
inj-insert-right2 {{ w = sift w }} (injr there) = injr (inj-insert-right2 {{w}} there)


--I need to rename this
proj-ret-left2 : {a b : Level}
        {E Here There : Effect2 {a} {b}}
        -> {{ w : EffectStorage2 E Here There }}
        -> {op : Op Here}
        -> Ret E (inj-insert-left2 op)
        -> Ret Here op
proj-ret-left2 {{ insert }} x = x
proj-ret-left2 {{ sift w }} x = proj-ret-left2 {{w}} x


--I need to rename this
proj-ret-right2 : {a b : Level}
        {E Here There : Effect2 {a} {b}}
        -> {{ w : EffectStorage2 E Here There }}
        -> {op : Op There}
        -> Ret E (inj-insert-right2 op)
        -> Ret There op
proj-ret-right2 {{ insert }} x =  x
proj-ret-right2 ⦃ w = sift w ⦄ {injl next } x = x
proj-ret-right2 ⦃ w = sift w ⦄ {injr op} x = proj-ret-right2 {{w}} x

injl-ret-eq2 : {a b : Level}
        {E Here There : Effect2 {a} {b}}
        -> {{ w : EffectStorage2 E Here There }}
        -> (op : Op Here)
        -> Ret E (inj-insert-left2 op) ≡ Ret Here op
injl-ret-eq2 ⦃ insert ⦄ _ = refl
injl-ret-eq2 ⦃ sift w ⦄ = injl-ret-eq2 {{w}}

injr-ret-eq2 : {a b : Level}
        {E Here There : Effect2 {a} {b}}
        -> {{ w : EffectStorage2 E Here There }}
        -> (op : Op There)
        -> Ret E (inj-insert-right2 op) ≡ Ret There op
injr-ret-eq2 ⦃ insert ⦄ _ = refl
injr-ret-eq2 ⦃ w = sift w ⦄ (injl x) = refl
injr-ret-eq2 ⦃ w = sift w ⦄ (injr y) = injr-ret-eq2 {{w}} y

case2 :  {a b : Level} {E Here There : Effect2 {a} {b}}
       -> {{ w : EffectStorage2 E Here There }}
        -> Op E
        -> (Op Here -> A )
        -> (Op There -> A )
        -> A
case2 {{ w = insert }} (injl here) fromHere fromThere = fromHere here
case2 {{ w = insert }} (injr there) fromHere fromThere = fromThere there
case2 {{ w = sift w }} (injl there) fromHere fromThere = fromThere (injl there)
case2 {{ w = sift w }} (injr e) fromHere fromThere = case2 {{w}} e fromHere λ there -> fromThere (injr there)

case-eq2 :  {a b : Level}{E Here There : Effect2 {a} {b}}
       -> {{ w : EffectStorage2 E Here There }}
        -> (op : Op E)
        -> ((op' : Op Here)  -> (op ≡ inj-insert-left2  op') -> A)
        -> ((op' : Op There) -> (op ≡ inj-insert-right2 op') -> A)
        -> A
case-eq2 {{ w = insert }} (injl x) eq-here eq-there = eq-here  x refl
case-eq2 {{ w = insert }} (injr y) eq-here eq-there = eq-there y refl
case-eq2 {{ w = sift w }} (injl x) eq-here eq-there = eq-there (injl x) refl
case-eq2 {{ w = sift w }} (injr e) eq-here eq-there =
    case-eq2 {{w}} e
        (λ  here eq -> eq-here  here (cong injr eq))
        (λ there eq -> eq-there (injr there) (cong injr eq))

subst2 : {a : Level} {A : Set a} {x y : A} (P : A → Set b)
  → x ≡ y
    ---------
  → P x → P y
subst2 P refl px = px



help21 :  {a b : Level} {E Here There : Effect2 {a} {b}}
       -> {{ w   : EffectStorage2 E Here There }}
       -> (  op' : Op Here)
       -> (  op  : Op E)
       -> (  eq  : op ≡ inj-insert-left2 op')
       -> Ret Here op'
       -> Ret E    op
help21 {a} {b} {E} {Here} ⦃ w ⦄ op' op eq = subst2 {b} id (begin
        Ret Here op'
        ≡⟨ sym (injl-ret-eq2 {{w}} op')  ⟩
        Ret E (inj-insert-left2 op')
        ≡⟨ sym (cong (Ret E) eq)  ⟩
        Ret E op
        ∎)

help22 :  {a b : Level} {E Here There : Effect2 {a} {b}}
       -> {{ w   : EffectStorage2 E Here There }}
       -> (  op' : Op There)
       -> (  op  : Op E)
       -> (  eq  : op ≡ inj-insert-right2 op')
       -> Ret There op'
       -> Ret E    op
help22 {a} {b} {E} {Here} {There} ⦃ w ⦄ op' op eq = subst2 {b} id (begin
        Ret There op'
        ≡⟨ sym (injr-ret-eq2 {{w}} op')  ⟩
        Ret E (inj-insert-right2 op')
        ≡⟨ sym (cong (Ret E) eq)  ⟩
        Ret E op
        ∎)

-- What doest it do?
-- How doest it do?
to-front2 :  {a b : Level} {E Here There : Effect2 {a} {b}}
          -> {A : Set b}
          -> {{ w : EffectStorage2 E Here There }}
          -> Free2 E A
          -> Free2 (coProduct2 Here There) A
to-front2 ⦃ w = w ⦄ (pure x) = pure x
to-front2 ⦃ w = insert ⦄ (impure op k) = impure op
                            (λ x -> to-front2 {{insert}} (k x))
to-front2 ⦃ w = sift w ⦄ (impure (injl op) k) =
    impure (injr (injl op)) (λ x -> to-front2 {{sift w}} (k x))
to-front2 { Here = Here } {{ sift {E = E} {There = There} w }} (impure (injr op) k) = case-eq2 {{ w }} op
    (λ op' eq -> impure (injl op') λ x -> to-front2 {{sift w}} (k (help21  {{w}} op' op eq x)))
    (λ op' eq -> impure (injr (injr op')) λ x -> to-front2 {{sift w}} (k (help22 {{w}} op' op eq x)))

-- I am not sure about levels
Alg2 : {a b : Level }(Eff : Effect2 {a} {b}) -> (A : Set b) -> Set (a ⊔ b)
Alg2 Eff A = (op : Op Eff)(k : Ret Eff op -> (A)) -> A

fold2 : {a b : Level } {A : Set b} {B : Set b} {Eff : Effect2 {a} {b}}
        -> (A -> B)
        -> Alg2 Eff B
        -> Free2 {a} {b} Eff A
        -> B
fold2 g alg (pure x) = g x
fold2 g alg (impure op k) = alg op λ x -> fold2 g alg (k x)


Alg3 : {a b : Level }(Eff : Effect2 {a} {b}) -> (A : Set (lsuc a ⊔ lsuc b)) -> Set (lsuc a ⊔ lsuc b)
Alg3 Eff A = (op : Op Eff)(k : Ret Eff op -> (A)) -> A

fold3 : {a b : Level } {A : Set b} {B : Set (lsuc a  ⊔ lsuc b)} {Eff : Effect2 {a} {b}}
        -> (A -> B)
        -> Alg3 Eff B
        -> Free2 {a} {b} Eff A
        -> B
fold3 g alg (pure x) = g x
fold3 g alg (impure op k) = alg op λ x -> fold3 g alg (k x)

-- How does it work?
_>>=_ : {a b : Level} {A : Set b} {B : Set b}
        {Eff : Effect2 {a} {b}} -> Free2 Eff A -> (A -> Free2 Eff B) -> Free2 Eff B
m >>= g = fold3 g impure m

-- How does it work?
_>>_ : {a b : Level} {A : Set b} {B : Set b}
       {Eff : Effect2 {a} {b}} ->
     Free2 Eff A → Free2 Eff B → Free2 Eff B
m1 >> m2 = m1 >>= λ _ → m2


record Handler2 {a b : Level}
                (A : Set b)
                (E : Effect2 {a} {b})
                (P : Set b)
                (B : Set b)
                (Continue : Effect2 {a} {b})
                : Set (lsuc (a ⊔ b))
                where
    field ret : A -> P -> Free2 Continue B
          hdl : Alg3 E (P -> Free2 Continue B)
open Handler2 public

givenHandle2 : {a b : Level}
            {A : Set b}
            {B : Set b}
            {P : Set b}
            -> {E Here There : Effect2 {a} {b}}
            -> {{ EffectStorage2 E Here There  }}
            -> Handler2 A Here P B There
            -> Free2 E A
            -> (P -> Free2 {a} {b} There B)
givenHandle2 {a} {b} {A} {B} {P} {E} {Here} {There} h eff =
    fold3 (ret h) func (to-front2 eff) where
    func : Alg3 (coProduct2 Here There) (P -> Free2 {a} {b} There B)
    func  (injl op) k p = hdl h op k p
    func (injr op) k p = impure op (λ x → k x p)
