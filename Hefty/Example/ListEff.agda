{-# OPTIONS  --backtracking-instance-search  #-}
module Example.ListEff where

open import Agda.Builtin.Unit
open import Agda.Builtin.Nat
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
    m n : Nat


record Effect : Set₁ where
 field Op  : Set
       Ret : Op -> Set

open Effect public

variable
    Eff  : Effect
    Eff1  : Effect
    Eff2  : Effect



data Free (eff : Effect) ( A : Set) : Set where
    pure   : A                                               -> Free eff A
    impure : (op : Op eff) -> (k : Ret eff op -> Free eff A) -> Free eff A

coProduct : Effect -> Effect -> Effect
Op  (coProduct a b) = Sum (Op a)  (Op b)
Ret (coProduct a b) x = elim (Ret a) (Ret b) x

infixr 12 _|>_
_|>_ : Effect -> Effect -> Effect
a |> b  = coProduct a b



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

data TeletypeOp : Set where
  putChar  : Char   -> TeletypeOp
  getChar  : TeletypeOp

Teletype : Effect
Teletype .Op              = TeletypeOp
Teletype .Ret (putChar x) = ⊤
Teletype .Ret getChar     = Char

data FileSystemOp : Set where
  ReadFile   : String -> FileSystemOp
  WriteFile  : String -> String -> FileSystemOp

Filesystem : Effect
Filesystem .Op                        = FileSystemOp
Filesystem .Ret (ReadFile file)       = String
Filesystem .Ret (WriteFile file text) = ⊤



data EffectRow1 : List Effect -> Set2 where
  here  : (eff : Effect) -> EffectRow1 ( eff ∷ [])
  there :    {n : List Effect}
          -> (eff : Effect)
          -> (xs : EffectRow1 n)
          ->  EffectRow1 ( eff ∷ n )



[_] : {a : Level}{A : Set a} -> A ->  List A
[ x ] = x ∷ []
{-
inj-left : {E Here : Effect}
          -> EffectRow1 []
          -> Op Here
          -> Op E
inj-left  = {!!}
-}

{-
data EffectRow  : Effect -> Effect -> Set₁ where
    insert  : {E Tail : Effect}
            -> EffectRow E (E |> Tail)
    sift    : {Result E E2 Tail : Effect}
            -> EffectRow E Result
            -> EffectRow E (E2 |> Result)


inj-left : {E Here : Effect}
                  {{ w : EffectRow  Here E }}
                  -> Op Here
                  -> Op E
inj-left {{ insert }} op = injl op
inj-left {{ sift w }} op = injr (inj-left {{w}} op)


inj-right : {E Here : Effect}
            {{ w : EffectRow Here E}}
            -> Op There  <----- PROBLEM
            -> Op E
inj-right {{ insert }} op = injr op
inj-right {{ w = sift w }} (injl next) = injl next
inj-right {{ w = sift w }} (injr there) = injr (inj-insert-right {{w}} there)

data EffectRow  : -> Set₁ where
    insert  : {E Tail : Effect}
            -> EffectRow E (E |> Tail)
    sift    : {Result E E2 Tail : Effect}
            -> EffectRow E Result
            -> EffectRow E (E2 |> Result)


data IN  : Effect -> EffectRow where


-}




























-- Fin n is a type with n elements.

data Fin : Nat → Set where
  zero : Fin (suc n)
  suc  : (i : Fin n) → Fin (suc n)


data Vec (A : Set a) : Nat → Set a where
  []  : Vec A zero
  _∷_ : ∀ (x : A) (xs : Vec A n) → Vec A (suc n)

infix 4 _[_]=_

data _[_]=_ {A : Set a} : Vec A n → Fin n → A → Set a where
  here  : ∀     {x}   {xs : Vec A n} → x ∷ xs [ zero ]= x
  there : ∀ {i} {x y} {xs : Vec A n}
    (xs[i]=x : xs [ i ]= x) → y ∷ xs [ suc i ]= x
