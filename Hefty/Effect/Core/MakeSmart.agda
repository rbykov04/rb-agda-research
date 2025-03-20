module Effect.Core.MakeSmart where

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

open import Effect.Core.Free2 hiding ( _>>=_ ; _>>_ )
open import Effect.Free2.IO hiding (return; _>>_; _>>=_)

private
  variable
    a b c d e : Level
    A : Set a
    B : Set b
    C : Set c
    D : Set d
    E : Set e



infixl 1 _>>_
_>>=_ : TC A → (A -> TC B) → TC B
t1 >>= t2 = bindTC t1 t2

_>>_ : TC A → TC B → TC B
a >> b = a >>= \ _ → b



mkArg : {A : Set} -> Visibility -> A -> Arg A
mkArg v = arg (arg-info v (modality relevant quantity-ω))


-- Defining: id-name {A} x = x
defId : (id-name : Name) → TC ⊤
defId id-name = defineFun id-name
  ( clause (
            (   "A", mkArg visible (agda-sort (lit 0) ))
            ∷ ("x", mkArg visible (var 0 []))
            ∷  [])
          (  mkArg  hidden (var 1)
          ∷ mkArg visible (var 0)
          ∷ [])
          (var 0 [])
  ∷ [])

id2 : {A : Set} (x : A) → A
unquoteDef id2 = defId id2


call : Name -> List (Arg Term) -> Arg Term
call f args = mkArg visible (def f args)

callC : Name -> List (Arg Term) -> Arg Term
callC f args = mkArg visible (con f args)


localVar : Nat -> Arg Term
localVar n = mkArg visible (var n [])

[_] : A → List A
[ x ] = x ∷ []

smart-constr1-def : Name -> Name -> TC ⊤
smart-constr1-def id-name op-name = defineFun id-name
  ( [ clause (
              ("w", mkArg instance′ (var 0 []))
            ∷ ("v", mkArg visible (var 1 []))
            ∷  [])
          (  mkArg  instance′ (var 1)
          ∷ mkArg visible (var 0)
          ∷ [])
          (con (quote impure) (
              (call (quote inj-insert-left2)
                ([ callC op-name [ (localVar 0) ] ]))
                ∷ mkArg visible (lam visible
                  (abs "x" (con (quote pure)
                        [ call (quote proj-ret-left2) (
                          (mkArg instance′ (var 2 []))
                       ∷ (mkArg visible (var 0 []))
                       ∷ [] ) ])))
                ∷ []))
   ])

mkSmart1 : Name -> Effect2 {lsuc lzero} {_} -> Name → Set -> Set -> TC ⊤
mkSmart1 id-name eff op-name in-type ret-type = do
  ty <- quoteTC ({E There : Effect2}
                -> {{ EffectStorage2 E eff There}}
                -> in-type
                -> Free2  E ret-type)
  declareDef (mkArg visible id-name) ty
  smart-constr1-def id-name op-name


smart-constr0-def : Name -> Name -> TC ⊤
smart-constr0-def id-name op-name = defineFun id-name
  ( [ clause (
              ("w", mkArg instance′ (var 0 []))
            ∷  [])
          (  mkArg  instance′ (var 0)
          ∷ [])
          (con (quote impure) (
              (call (quote inj-insert-left2)
                ([ callC op-name [] ]))
                ∷ mkArg visible (lam visible
                  (abs "x" (con (quote pure)
                        [ call (quote proj-ret-left2) (
                          (mkArg instance′ (var 1 []))
                       ∷ (mkArg visible (var 0 []))
                       ∷ [] ) ])))
                ∷ []))
   ])

mkSmart0 : Name -> Effect2 {lsuc lzero} {_} -> Name → Set -> TC ⊤
mkSmart0 id-name eff op-name ret-type  = do
  ty <- quoteTC ({E There : Effect2}
                -> {{ EffectStorage2 E eff There}}
                -> Free2  E ret-type)
  declareDef (mkArg visible id-name) ty
  smart-constr0-def id-name op-name


data TestOp : Set1 where
  put  : Char   -> TestOp
  get  : TestOp

Test' : Effect2
Test' .Op          = TestOp
Test' .Ret (put x) = ⊤
Test' .Ret get     = Char


unquoteDecl testPut = mkSmart1 testPut Test' (quote put) Char ⊤
unquoteDecl testGet = mkSmart0 testGet Test' (quote get) Char

test1 : {E There : Effect2} -> {{ EffectStorage2 E Test' There }} -> Free2 E ⊤
test1  = testPut 'x'

test2 : {E There : Effect2} -> {{ EffectStorage2 E Test' There }} -> Free2 E Char
test2  = testGet

{-
Req : {a b : Level}
      -> {There : Effect2 {a} {b}}
      -> (E : Effect2 {a} {b})
      -> (Eff : Effect2 {a} {b})
      -> Set (lsuc a ⊔ lsuc b)
Req {a} {b} {There} E Eff = EffectStorage2 E Eff There

test3 : {E : Effect2} -> Req E Test' -> Free2 E ⊤
test3  = testPut 'x'
mk : {There : Effect2}
    -> (E : Effect2)
    -> (Here : Effect2)
    -> {{ EffectStorage2 E Here There }}

{{ mk E Teletype }}
-}
