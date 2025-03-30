module Foundation.Base
    where

open import Agda.Primitive public
open import Agda.Builtin.Bool
open import Agda.Builtin.String
open import Agda.Builtin.Unit
open import Agda.Builtin.List
open import Agda.Builtin.Maybe
open import Agda.Builtin.Nat
open import Agda.Builtin.Equality
open import Agda.Builtin.IO
open import Agda.Builtin.Unit
open import Agda.Builtin.Sigma
open import Agda.Primitive




private
  variable
    a b c d e : Level
    A : Set a
    B : Set b
    C : Set c
    D : Set d
    E : Set e



infixr 70 _⊎_
data _⊎_ {ℓa ℓb} (A : Set ℓa) (B : Set ℓb) : Set (ℓa ⊔ ℓb) where
  inl : A → A ⊎ B
  inr : B → A ⊎ B

elim : {ℓa ℓb : Level} {A : Set ℓa} {B : Set ℓb}
       {ℓ : Level} {C : A ⊎ B → Set ℓ}
       (f : (a : A) → C (inl a)) (g : (b : B) → C (inr b))
     → (s : A ⊎ B) → C s
elim f _ (inl x) = f x
elim _ g (inr x) = g x

infix 0 if_then_else_

if_then_else_ : Bool → A → A → A
if true  then t else f = t
if false then t else f = f

infixr 6 _∧_
infixr 5 _∨_


_∧_ : Bool → Bool → Bool
true  ∧ b = b
false ∧ b = false

_∨_ : Bool → Bool → Bool
true  ∨ b = true
false ∨ b = b


case_of_ : A -> (A -> B) -> B
case x of f = f x

infixr 12 _++_
_++_ : String -> String -> String
a ++ b = primStringAppend a b

_∷ʳ_ : {A : Set} → List A → A → List A
[] ∷ʳ a = a ∷ []
(x ∷ xs) ∷ʳ a = x ∷ ( xs ∷ʳ a  )



data ⊥ : Set where
⊥-elim : ∀ {w} {Whatever : Set w} → ⊥ → Whatever
⊥-elim ()

---
-- also know as ( , )
infixr 2 _×_
_×_ : ∀ (A : Set a) (B : Set b) → Set (a ⊔ b)
_×_ {a} {b} A B = Σ A (λ x -> B)


id : A -> A
id x = x

_$_ : ∀ {A : Set a} {B : A → Set b} →
      ((x : A) → B x) → ((x : A) → B x)
f $ x = f x
{-# INLINE _$_ #-}

cong : (f : A -> B) {x y : A}
  -> x ≡ y
    ---------
  -> f x ≡ f y
cong f refl  =  refl

cong2 : {a : Level} {A : Set a}(f : A -> B) {x y : A}
  -> x ≡ y
    ---------
  -> f x ≡ f y
cong2 f refl  =  refl



trans :  {x y z : A}
  → x ≡ y
  → y ≡ z
    -----
  → x ≡ z
trans refl refl  =  refl

trans2 : {a : Level} {A : Set a} {x y z : A }
  → x ≡ y
  → y ≡ z
    -----
  → x ≡ z
trans2 refl refl  =  refl

subst :  {x y : A} (P : A → Set)
  → x ≡ y
    ---------
  → P x → P y
subst P refl px = px

subst2 : {a : Level} {A : Set a} {x y : A} (P : A → Set b)
  → x ≡ y
    ---------
  → P x → P y
subst2 P refl px = px



infix  1 begin_
infixr 2 step-≡-∣ step-≡-⟩
infix  3 _∎

begin_ : ∀ {x y : A} → x ≡ y → x ≡ y
begin x≡y  =  x≡y

step-≡-∣ : ∀ (x : A) {y : A} → x ≡ y → x ≡ y
step-≡-∣ x x≡y  =  x≡y

step-≡-⟩ : ∀ (x : A) {y z : A} → y ≡ z → x ≡ y → x ≡ z
step-≡-⟩ x y≡z x≡y  =  trans x≡y y≡z

syntax step-≡-∣ x x≡y      =  x ≡⟨⟩ x≡y
syntax step-≡-⟩ x y≡z x≡y  =  x ≡⟨  x≡y ⟩ y≡z
_∎ : ∀ (x : A) → x ≡ x
x ∎  =  refl

sym : ∀ {A : Set a} {x y : A}
  → x ≡ y
    -----
  → y ≡ x
sym refl = refl

sym2 : ∀ {A : Set a} {x y : A}
  → x ≡ y
    -----
  → y ≡ x
sym2 refl = refl
