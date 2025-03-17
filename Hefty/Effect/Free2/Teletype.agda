{-# OPTIONS  --backtracking-instance-search  #-}
module Effect.Free2.Teletype where

open import Agda.Builtin.Unit
open import Agda.Builtin.Sigma
open import Agda.Builtin.List
open import Agda.Builtin.Char
open import Agda.Builtin.String
open import Agda.Builtin.IO
open import Agda.Builtin.Equality
open import Agda.Primitive

open import Mystdlib.Mystdlib

open import Effect.Core.Free2 hiding ( _>>_; _>>=_)

open import Effect.Free2.IO hiding (return; _>>_; _>>=_)
private
  variable
    a b c d e : Level
    A : Set a
    B : Set b
    C : Set c
    D : Set d
    E : Set e


postulate
    putCharIO : Char -> IO ⊤
    getCharIO : IO Char
{-# FOREIGN GHC import qualified Data.Text as T #-}
{-# FOREIGN GHC import qualified System.IO as SIO #-}
{-# COMPILE GHC putCharIO = (SIO.hPutChar SIO.stderr) #-}
{-# COMPILE GHC getCharIO = SIO.getChar #-}



data TeletypeOp : Set1 where
  putChar  : Char   -> TeletypeOp
  getChar  : TeletypeOp

Teletype : Effect2
Teletype .Op              = TeletypeOp
Teletype .Ret (putChar x) = ⊤
Teletype .Ret getChar     = Char

hTeletype : Handler2 A Teletype ⊤ ( ⊤ ) IOEF
hTeletype .ret _ _ = pure tt
hTeletype .hdl (putChar ch) k _ = impure (liftIO ⊤ (putCharIO ch)) (k tt )
hTeletype .hdl getChar k _      = impure (liftIO Char (getCharIO)) \ ch -> k ch tt

hTeletype2 :  {E Here : Effect2}
            -> {{ EffectStorage2 E Here IOEF}}
            -> Handler2 A Teletype ⊤ ( ⊤ ) E
hTeletype2 .ret _ _ = pure tt
hTeletype2 {{w}} .hdl (putChar ch) k oo       =
  impure
    (inj-insert-right2 {{w}}(liftIO ⊤ (putCharIO ch)))
    \ ch -> k (proj-ret-right2 {{w}} ch) tt
hTeletype2 {{w}} .hdl getChar k _ =
  impure
    (inj-insert-right2  (liftIO Char getCharIO ))
    \ x -> k (proj-ret-right2 {{w}} x ) tt




`putChar :
      {E There : Effect2}
     -> {{ EffectStorage2 E Teletype There}}
     -> Char
     -> Free2 E ⊤
`putChar {{ w }} ch = impure (inj-insert-left2 (putChar ch)) (λ x -> pure (proj-ret-left2 {{w}} x))

`getChar :
      {E There : Effect2}
     -> {{ EffectStorage2 E Teletype There}}
     -> Free2 E Char
`getChar {{ w }} = impure (inj-insert-left2 getChar) (λ x -> pure (proj-ret-left2 {{w}} x))

putStrLn :
        {E There : Effect2}
          -> {{ EffectStorage2 E Teletype There }}
          -> String
          -> Free2 E ⊤
putStrLn x = f (primStringToList x) where
  f : List Char
    -> {E There : Effect2}
    -> {{ EffectStorage2 E Teletype There}}
    -> Free2 E ⊤
  f [] =  `putChar '\n'
  f (x ∷ str) = do
    `putChar x
    f str
    where open import Effect.Core.Free2 using (_>>=_; _>>_)
