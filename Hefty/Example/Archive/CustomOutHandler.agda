{-# OPTIONS  --backtracking-instance-search  #-}
module Example.CustomOutHandler where

open import Agda.Builtin.Unit
open import Agda.Builtin.Sigma
open import Agda.Builtin.IO
open import Agda.Primitive

open import Mystdlib.Mystdlib
open import Mystdlib.IO

open import Effect.Core.Free hiding (_>>=_; _>>_)
open import Effect.Free.Output
open import Effect.Free.Nil

private
  variable
    a b c d e : Level
    A : Set a
    B : Set b
    C : Set c
    D : Set d
    E : Set e


program : Free (coProduct Output Nil) ⊤
program = do `out "Hello";
              `out " ";
              `out "world!\n"
  where open import Effect.Core.Free using (_>>=_; _>>_)


hOutIO : {Eff : Effect} -> Handler A Output ⊤ ( A × IO ⊤ ) Eff
ret hOutIO x _ = pure (x , return tt)
hdl hOutIO (out s) k p = do
    (x , s') <- k tt p
    pure (x , (putStr s >>> s'))
  where open import Effect.Core.Free using (_>>=_; _>>_)



main : IO ⊤
main = snd (un ((givenHandle hOutIO program) tt))

