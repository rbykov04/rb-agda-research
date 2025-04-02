module Control.Effect.Algebraic.Effect.RowInsert
    where

open import Agda.Builtin.Equality
open import Foundation.Base
open import Control.Effect.Algebraic.Effect
open import Control.Effect.Algebraic.Effect.Free

private
  variable
    a b c d e o r : Level
    A : Set a
    B : Set b
    C : Set c
    D : Set d
    E : Set e




data EffectStorage {a b : Level} :
                       Effect {a} {b}
                    -> Effect {a} {b}
                    -> Effect {a} {b}
                    -> Set (lsuc (a ⊔ b))
                    where
    insert  : {Here There : Effect {a} {b}}
            -> EffectStorage {a} {b} (Here ⊕ There) Here There
    sift  : {E Here Next There : Effect {a} {b}}
            -> EffectStorage {a} {b} E Here There
            -> EffectStorage {a} {b} (Next ⊕ E) Here (Next ⊕ There)
open EffectStorage


effrow_＝_∣_ : (Row E Compl : Effect {o} {r}) -> Set (lsuc (o  ⊔ r))
effrow Row ＝ E ∣ Compl = EffectStorage Row E Compl

instance
  insert21 : {a b : Level}
            -> {Here There : Effect {a} {b}}
            -> EffectStorage {a} {b} (Here ⊕ There) Here There
  insert21 = insert
  {-# OVERLAPS insert21 #-}

  sift21 : {a b : Level}
          {E Here Next There : Effect {a} {b}}
        -> {{EffectStorage E Here There}}
        -> (EffectStorage (Next ⊕ E) Here (Next ⊕ There))
  sift21 ⦃ w ⦄ = sift w
  {-# OVERLAPS sift21 #-}



--I need to rename this
inj-insert-left2 : {a b : Level} {E Here There : Effect {a} {b}}
                  {{ w : EffectStorage E Here There }}
                  -> Op Here
                  -> Op E
inj-insert-left2 {{ insert }} op = inl op
inj-insert-left2 {{ sift w }} op = inr (inj-insert-left2 {{w}} op)

inj-insert-right2 :  {a b : Level} {E Here There : Effect {a} {b}} {{ w : EffectStorage E Here There }}  -> Op There -> Op E
inj-insert-right2 {{ insert }} op = inr op
inj-insert-right2 {{ w = sift w }} (inl next) = inl next
inj-insert-right2 {{ w = sift w }} (inr there) = inr (inj-insert-right2 {{w}} there)


--I need to rename this
proj-ret-left2 : {a b : Level}
        {E Here There : Effect {a} {b}}
        -> {{ w : EffectStorage E Here There }}
        -> {op : Op Here}
        -> Ret E (inj-insert-left2 op)
        -> Ret Here op
proj-ret-left2 {{ insert }} x = x
proj-ret-left2 {{ sift w }} x = proj-ret-left2 {{w}} x


--I need to rename this
proj-ret-right2 : {a b : Level}
        {E Here There : Effect {a} {b}}
        -> {{ w : EffectStorage E Here There }}
        -> {op : Op There}
        -> Ret E (inj-insert-right2 op)
        -> Ret There op
proj-ret-right2 {{ insert }} x =  x
proj-ret-right2 ⦃ w = sift w ⦄ {inl next } x = x
proj-ret-right2 ⦃ w = sift w ⦄ {inr op} x = proj-ret-right2 {{w}} x

inl-ret-eq2 : {a b : Level}
        {E Here There : Effect {a} {b}}
        -> {{ w : EffectStorage E Here There }}
        -> (op : Op Here)
        -> Ret E (inj-insert-left2 op) ≡ Ret Here op
inl-ret-eq2 ⦃ insert ⦄ _ = refl
inl-ret-eq2 ⦃ sift w ⦄ = inl-ret-eq2 {{w}}

inr-ret-eq2 : {a b : Level}
        {E Here There : Effect {a} {b}}
        -> {{ w : EffectStorage E Here There }}
        -> (op : Op There)
        -> Ret E (inj-insert-right2 op) ≡ Ret There op
inr-ret-eq2 ⦃ insert ⦄ _ = refl
inr-ret-eq2 ⦃ w = sift w ⦄ (inl x) = refl
inr-ret-eq2 ⦃ w = sift w ⦄ (inr y) = inr-ret-eq2 {{w}} y

case2 :  {a b : Level} {E Here There : Effect {a} {b}}
       -> {{ w : EffectStorage E Here There }}
        -> Op E
        -> (Op Here -> A )
        -> (Op There -> A )
        -> A
case2 {{ w = insert }} (inl here) fromHere fromThere = fromHere here
case2 {{ w = insert }} (inr there) fromHere fromThere = fromThere there
case2 {{ w = sift w }} (inl there) fromHere fromThere = fromThere (inl there)
case2 {{ w = sift w }} (inr e) fromHere fromThere = case2 {{w}} e fromHere λ there -> fromThere (inr there)

case-eq2 :  {a b : Level}{E Here There : Effect {a} {b}}
       -> {{ w : EffectStorage E Here There }}
        -> (op : Op E)
        -> ((op' : Op Here)  -> (op ≡ inj-insert-left2  op') -> A)
        -> ((op' : Op There) -> (op ≡ inj-insert-right2 op') -> A)
        -> A
case-eq2 {{ w = insert }} (inl x) eq-here eq-there = eq-here  x refl
case-eq2 {{ w = insert }} (inr y) eq-here eq-there = eq-there y refl
case-eq2 {{ w = sift w }} (inl x) eq-here eq-there = eq-there (inl x) refl
case-eq2 {{ w = sift w }} (inr e) eq-here eq-there =
    case-eq2 {{w}} e
        (λ  here eq -> eq-here  here (cong inr eq))
        (λ there eq -> eq-there (inr there) (cong inr eq))


help21 :  {a b : Level} {E Here There : Effect {a} {b}}
       -> {{ w   : EffectStorage E Here There }}
       -> (  op' : Op Here)
       -> (  op  : Op E)
       -> (  eq  : op ≡ inj-insert-left2 op')
       -> Ret Here op'
       -> Ret E    op
help21 {a} {b} {E} {Here} ⦃ w ⦄ op' op eq = subst2 {b} id (begin
        Ret Here op'
        ≡⟨ sym (inl-ret-eq2 {{w}} op')  ⟩
        Ret E (inj-insert-left2 op')
        ≡⟨ sym (cong (Ret E) eq)  ⟩
        Ret E op
        ∎)

help22 :  {a b : Level} {E Here There : Effect {a} {b}}
       -> {{ w   : EffectStorage E Here There }}
       -> (  op' : Op There)
       -> (  op  : Op E)
       -> (  eq  : op ≡ inj-insert-right2 op')
       -> Ret There op'
       -> Ret E    op
help22 {a} {b} {E} {Here} {There} ⦃ w ⦄ op' op eq = subst2 {b} id (begin
        Ret There op'
        ≡⟨ sym (inr-ret-eq2 {{w}} op')  ⟩
        Ret E (inj-insert-right2 op')
        ≡⟨ sym (cong (Ret E) eq)  ⟩
        Ret E op
        ∎)

-- What doest it do?
-- How doest it do?
to-front :  {a b : Level} {E Here There : Effect {a} {b}}
          -> {A : Set b}
          -> {{ w : EffectStorage E Here There }}
          -> Free E A
          -> Free (Here ⊕ There) A
to-front ⦃ w = w ⦄ (pure x) = pure x
to-front ⦃ w = insert ⦄ (impure op k) = impure op
                            (λ x -> to-front {{insert}} (k x))
to-front ⦃ w = sift w ⦄ (impure (inl op) k) =
    impure (inr (inl op)) (λ x -> to-front {{sift w}} (k x))
to-front { Here = Here } {{ sift {E = E} {There = There} w }} (impure (inr op) k) = case-eq2 {{ w }} op
    (λ op' eq -> impure (inl op') λ x -> to-front {{sift w}} (k (help21  {{w}} op' op eq x)))
    (λ op' eq -> impure (inr (inr op')) λ x -> to-front {{sift w}} (k (help22 {{w}} op' op eq x)))

record Handler {a b : Level}
                (A : Set b)
                (E : Effect {a} {b})
                (P : Set b)
                (B : Set b)
                (Continue : Effect {a} {b})
                : Set (lsuc (a ⊔ b))
                where
    field ret : A -> P -> Free Continue B
          hdl : Alg E (P -> Free Continue B)
open Handler public

givenHandle : {a b : Level}
            {A : Set b}
            {B : Set b}
            {P : Set b}
            -> {E Here There : Effect {a} {b}}
            -> {{ EffectStorage E Here There  }}
            -> Handler A Here P B There
            -> Free E A
            -> (P -> Free {a} {b} There B)
givenHandle {a} {b} {A} {B} {P} {E} {Here} {There} h eff =
    fold (ret h) func (to-front eff) where
    func : Alg (Here ⊕ There) (P -> Free {a} {b} There B)
    func  (inl op) k p = hdl h op k p
    func (inr op) k p = impure op (λ x → k x p)


#_ : {a b : Level} {Eff Eff0 Eff' : Effect {a} {b}}
     -> {{w : EffectStorage Eff Eff0 Eff'}}
     -> Free Eff' A
     -> Free Eff  A
#_ ⦃ w ⦄ = fold pure \ op' k → impure (inj-insert-right2 op')
                                      \ ret' → k (proj-ret-right2 {{w}} ret')

send : {a b : Level} {E Here There : Effect {a} {b}}
     -> {{ w : EffectStorage E Here There }}
     -> (op : Op Here)
     -> Free E (Ret Here op)
send {{w}} op = impure (inj-insert-left2 {{w}} op)
                      \ ret -> pure (proj-ret-left2 {{w}} ret)
