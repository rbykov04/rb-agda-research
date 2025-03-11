{-# OPTIONS  --backtracking-instance-search  #-}
module Example.Teletype where

open import Agda.Builtin.Unit
open import Agda.Builtin.Sigma
open import Agda.Builtin.List
open import Agda.Builtin.Char
open import Agda.Builtin.String
open import Agda.Builtin.IO
open import Agda.Primitive

open import Mystdlib.Mystdlib

open import Effect.Core.Free
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

data TeletypeOp : Set where
  putChar  : Char   -> TeletypeOp
  getChar  : TeletypeOp

Teletype : Effect
Teletype .Op              = TeletypeOp
Teletype .Ret (putChar x) = ⊤
Teletype .Ret getChar     = Char


`putChar :
      {E There : Effect}
     -> {{ EffectStorage E Teletype There }}
     -> Char
     -> Free E ⊤
`putChar {{ w }} n = impure (inj-insert-left (putChar n) ) (λ x -> pure (proj-ret-left {{w}} x))

`getChar :
      {E There : Effect}
     -> {{ EffectStorage E Teletype There }}
     -> Free E Char
`getChar {{ w }}  = impure (inj-insert-left getChar ) (λ x -> pure (proj-ret-left {{w}} x))



infixl 1 _>>>=_
postulate
    putCharIO : Char → IO ⊤
    getCharIO : IO Char
    return : A → IO A
    _>>>=_  : IO A → (A → IO B) → IO B


{-# FOREIGN GHC import qualified Data.Text as T #-}
{-# FOREIGN GHC import qualified System.IO as SIO #-}
{-# COMPILE GHC putCharIO = (SIO.hPutChar SIO.stderr) #-}
{-# COMPILE GHC getCharIO = SIO.getChar #-}
{-# COMPILE GHC return = \_ _ -> return    #-}
{-# COMPILE GHC _>>>=_  = \_ _ _ _ -> (>>=) #-}

infixl 1 _>>>_
_>>>_ : IO A → IO B → IO B
a >>> b = a >>>= λ _ → b

{-
hTeletype : {Eff : Effect} -> Handler A Teletype ⊤ ( A × IO ⊤ ) Eff
hTeletype .ret x t = pure (x , return tt)
hTeletype .hdl (putChar ch) k p = do
  (x , io) <- k tt p
  pure (x , (putCharIO ch >>> io))
hTeletype .hdl getChar k n = do
  (x , io) <- k '1' tt
  (x , io) <- k '2' tt
  pure (x , {!!})
--  pure (x , (getCharIO >>> io))
-}


hTeletype : {Eff : Effect} -> Handler A Teletype ⊤ (IO ⊤ × Char) Eff
hTeletype .ret x t = pure (return tt , ' ')
hTeletype .hdl (putChar ch) k p =  do
  (io , x) <- k tt p
  pure ( (putCharIO ch >>> io ) , x)

hTeletype .hdl getChar k n = do
  (io , x) <- pure ( (getCharIO >>>= \ x ->  {!!}) , ' ')
  k 'y' n


putStrLn : String -> Free (coProduct Teletype Nil) ⊤
putStrLn x = f (primStringToList x) where
  f : List Char ->  Free (coProduct Teletype Nil) ⊤
  f [] = `putChar '\n'
  f (x ∷ str) = do
    `putChar x
    f str

program : Free (coProduct Teletype Nil) ⊤
program = do
    putStrLn "Put"
    h1 <- `getChar
    `putChar h1
    `putChar h1
    putStrLn "Put2"
    h2 <- `getChar
    `putChar h2
    `putChar h2
    putStrLn "End"


main : IO ⊤
main = fst ( un ((givenHandle hTeletype program) tt))
