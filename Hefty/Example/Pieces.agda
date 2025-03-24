{-# OPTIONS  --backtracking-instance-search  #-}
module Example.Pieces where

open import Agda.Builtin.String
open import Agda.Builtin.Unit
open import Agda.Builtin.Bool
open import Agda.Builtin.List
open import Agda.Builtin.Nat
open import Agda.Builtin.Equality
open import Agda.Builtin.IO
open import Agda.Builtin.Unit
open import Agda.Builtin.String
open import Agda.Builtin.Sigma
open import Agda.Primitive

open import Mystdlib.Mystdlib
open import Effect.Core.Free hiding (_>>=_; _>>_)
open import Effect.Core.Hefty hiding (_>>=_; _>>_)
open import Effect.Free.Output
open import Effect.Free.Throw
open import Effect.Free.Nil
open import Effect.Free.State
open import Effect.Hefty.Lift

private
  variable
    a b c d e : Level
    A : Set a
    B : Set b
    C : Set c
    D : Set d
    E : Set e

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


hello-throw : Free (coProduct Output Throw) A
hello-throw = impure (injl (out "Hello")) (λ _ -> impure (injr throw) ⊥-elim)

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
{-
`incr :
      {E There : Effect}
     -> {{ EffectStorage E State There }}
     -> Free E ⊤
`incr  = do n <- `get; `put (1 + n)
  where open import Effect.Core.Free using (_>>=_; _>>_)

test-incr :
    un ((givenHandle hSt `incr ) 0) ≡ (tt , 1)
test-incr = refl
-}

hello-program : Free (coProduct Output Nil) ⊤
hello-program = do `out "Hello"; `out " "; `out "world!\n"
  where open import Effect.Core.Free using (_>>=_; _>>_)


test-hello :
    un ((givenHandle hOut hello-program) tt) ≡ (tt , "Hello world!\n")
test-hello = refl
