module Effect.Free.Output where

open import Agda.Builtin.String
open import Agda.Builtin.Unit
open import Agda.Builtin.Maybe
open import Agda.Builtin.Bool
open import Agda.Builtin.List
open import Agda.Builtin.Nat
open import Agda.Builtin.IO
open import Agda.Builtin.Unit
open import Agda.Builtin.String
open import Agda.Builtin.Sigma
open import Agda.Primitive

open import Mystdlib.Mystdlib
open import Mystdlib.Universe

open import Effect.Core.Free  hiding (_>>=_; _>>_)

private
  variable
    a b c d e : Level
    A : Set a
    B : Set b
    C : Set c
    D : Set d
    E : Set e


data OutOp : Set where
    out : String -> OutOp

Output : Effect
Op  Output = OutOp
Ret Output (out str) = ⊤

`out : {E There : Effect}
     -> {{ EffectStorage E Output There }}
     -> String
     -> Free E ⊤
`out {{ w }} str = impure (inj-insert-left (out str)) λ x -> pure ((proj-ret-left {{w}} x))

hOut : Handler A Output ⊤ ( A × String ) Eff
ret hOut x _ = pure (x , "")
hdl hOut (out s) k p = do (x , s') <- k tt p; pure (x , s ++ s')
  where open import Effect.Core.Free using (_>>=_; _>>_)
