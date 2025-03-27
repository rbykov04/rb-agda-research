{-# OPTIONS  --backtracking-instance-search  #-}
module Experimental.0-Free2List where

open import Agda.Builtin.Unit
open import Agda.Builtin.Nat
open import Agda.Builtin.Sigma
open import Agda.Builtin.List
open import Agda.Builtin.Char
open import Agda.Builtin.String
open import Agda.Builtin.IO
open import Agda.Builtin.Equality
open import Agda.Builtin.Reflection
open import Agda.Builtin.List
open import Agda.Primitive

open import Mystdlib.Mystdlib

open import Effect.Core.Free2 using (Effect2 ;  _|2>_ ; Op ; Ret ; subst2)
open import Effect.Free2.Teletype using (Teletype ; TeletypeOp ; getCharIO; putCharIO)
open import Effect.Free2.IO using (IOEF ; return; liftIO )
open import Effect.Free2.Filesystem using (Filesystem ; FileSystemOp)

private
  variable
    a b c d e : Level
    A : Set a
    B : Set b
    C : Set c
    D : Set d
    E : Set e

data Any {a b : Level}
         (P : Effect2 {a} {b} → Set (lsuc (a ⊔ b))) : List (Effect2 {a} {b}) → Set (lsuc (a ⊔ b)) where
  here  : ∀ {x : Effect2} {xs : List Effect2} → P x → Any P (x ∷ xs)
  there : ∀ {x : Effect2} {xs : List Effect2} → Any P xs → Any P (x ∷ xs)

infix 4 _∈_

_∈_ :{a b : Level} (x : Effect2 {a} {b}) (xs : List (Effect2 {a} {b})) → Set (lsuc a ⊔ lsuc b)
x ∈ xs = Any (x ≡_) xs


Alg : {a b : Level }
    {EffList : List (Effect2 {a} {b})}
    (Eff : Effect2 {a} {b})
    {{w : Eff ∈ EffList}}
    -> (A : Set b)
    -> Set (a ⊔ b)
Alg Eff {{w}} A = (op : Op Eff)(k : Ret Eff op -> (A)) -> A

data Free {a b : Level}
          (effList : List (Effect2 {a} {b}))
          (eff : Effect2 {a} {b})
          {{w : eff ∈ effList}}
          (A : Set b)
          : Set (lsuc (a ⊔ b)) where
      pure   : A -> Free effList eff A
      impure : (op : Op eff) -> (k : Ret eff op -> Free effList eff A) -> Free effList eff A


fold : {a b : Level }
        {A : Set b} {B : Set b}
        {effList : List (Effect2 {a} {b})}
        {eff : Effect2 {a} {b}}
        {{w : eff ∈ effList}}
        -> (A -> B)
        -> Alg eff B
        -> Free {a} {b} effList eff A
        -> B
fold ⦃ w ⦄ g alg (pure x) = g x
fold ⦃ w ⦄ g alg (impure op k) = alg op \ x → fold g alg (k x)

[_] : A → List A
[ x ] = x ∷ []


execAlgebra :
        { effList : List Effect2}
        {{ w : IOEF ∈ effList }}
        { A : Set  }
        -> Alg IOEF (IO A)
execAlgebra (Effect.Free2.IO.liftIO ty f) k = f >>= k
        where open import Effect.Free2.IO using (_>>=_; _>>_)

exec :
        { effList : List Effect2}
        {{ w : IOEF ∈ effList }}
        { A : Set  }
        -> Free effList IOEF A
        -> IO A
exec {effList} ⦃ w ⦄ {A} = fold  {{w}} return execAlgebra

program1 : Free [ IOEF ] IOEF {{here refl}} ⊤
program1 = impure (liftIO Char getCharIO) \ x ->
           impure (liftIO Char getCharIO) \ y ->
           impure (liftIO ⊤ (putCharIO y)) \ _ ->
           impure (liftIO ⊤ (putCharIO y)) \ _ ->
           impure (liftIO ⊤ (putCharIO y)) \ _ ->
           impure (liftIO ⊤ (putCharIO y)) \ _ ->
           impure (liftIO ⊤ (putCharIO y)) \ _ ->
           impure (liftIO ⊤ (putCharIO y)) \ _ ->
           pure tt


main : IO ⊤
main = exec  {{here refl}} program1
