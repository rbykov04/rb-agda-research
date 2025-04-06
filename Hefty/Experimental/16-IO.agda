--{-# OPTIONS  --backtracking-instance-search  #-}
module Experimental.16-IO
    where

open import Agda.Builtin.IO
open import Agda.Builtin.Unit
open import Agda.Builtin.Nat
open import Agda.Builtin.Bool
open import Agda.Builtin.String
open import Agda.Builtin.Char
open import Agda.Builtin.List
open import Agda.Primitive
open import Agda.Builtin.Equality
open import Foundation.Base

open import Control.Effect.Algebraic.Effect
open import Control.Effect.Algebraic.Hefty hiding (_>>=_; _>>_)
open import Control.Effect.Algebraic.Hefty.RowInsert hiding (inject)
open import Control.Effect.Algebraic.Effect.Free hiding (_>>=_; _>>_; fold)

--open import Control.Effect.Algebraic.HighOrder.Lift
--open import Control.Effect.Algebraic.HighOrder.Lift.RowInsert
--open import Control.Effect.Algebraic.Effect.RowInsert
open import Control.Effect.Algebraic.Effect.OpenUnion hiding (inject)
open import Control.Effect.Algebraic.Effect.OpenUnion.Properties


private
  variable
    a b c d e : Level
    A : Set a
    B : Set b
    C : Set c
    D : Set d
    E : Set e

postulate
    return : A → IO A
    _>>=IO_  : IO A → (A → IO B) → IO B
    putCharIO : Char -> IO ⊤
    getCharIO : IO Char
    readFileIO  : String -> IO String
    writeFileIO : String -> String -> IO ⊤
{-# FOREIGN GHC import qualified Data.Text as T #-}
{-# COMPILE GHC writeFileIO = \ path text -> writeFile (T.unpack path) (T.unpack text) #-}
{-# COMPILE GHC readFileIO = \ path ->  readFile (T.unpack path) >>= \ text -> return (T.pack text) #-}
{-# FOREIGN GHC import qualified Data.Text as T #-}
{-# FOREIGN GHC import qualified System.IO as SIO #-}
{-# COMPILE GHC putCharIO = (SIO.hPutChar SIO.stderr) #-}
{-# COMPILE GHC getCharIO = SIO.getChar #-}
{-# COMPILE GHC _>>=IO_  = \_ _ _ _ -> (>>=) #-}


IOEF : (A : Set) → Effect {lzero} {lzero}
IOEF A .Op = IO A
IOEF A .Ret x = IO A


hIO : {Eff : Effect {lzero} {lzero}}
    → ( B : Set )
    → Handler (IO A) (IOEF B) A (IO A) Eff
hIO A .ret x _ = pure x
hIO A .hdl op k x = k op x




Nil : Effect {lzero} {lzero}
Op  Nil = ⊥
Ret Nil = λ ()


un : Free Nil A -> A
un (pure x) = x

data TeletypeOp : Set where
  putChar  : Char   -> TeletypeOp
  getChar  : TeletypeOp



Teletype :  Effectᴴ {lzero} {lzero}
Teletype .Opᴴ = TeletypeOp
Teletype .Fork (putChar x) = IOEF ⊤
Teletype .Fork getChar = IOEF Char
Teletype .Retᴴ (putChar x) = IO ⊤
Teletype .Retᴴ getChar = IO Char


`putChar : {H H' : Effectᴴ}
      → {{heftyrow H ＝ Teletype ∣ H'}}
      → Char
      → Hefty H (IO ⊤)
`putChar  {{w}}  ch  =
    impure
        (inject {{w}} (putChar ch))
        (proj-fork-l {{w}} _ λ b → pure b)
        \ ret → pure ((proj-ret-l {{w}} ret))
    where open import Control.Effect.Algebraic.Hefty.RowInsert using (inject)


{-
putStrLn : {H H' : Effectᴴ}
    → {{heftyrow H ＝ Teletype ∣ H'}}
    → String
    → Hefty H ⊤
putStrLn str = f (primStringToList str) where
  f : {H H' : Effectᴴ}
    → {{heftyrow H ＝ Teletype ∣ H'}}
    → List Char → Hefty H ⊤
  f  [] = `putChar '\n'
  f (x ∷ str) = do
    `putChar x
    f str
    where open import Control.Effect.Algebraic.Hefty using (_>>=_; _>>_)
-}



cat : {Effs E : Effectᴴ {lzero} {lzero} }
      → {{heftyrow Effs ＝ Teletype ∣ E }}
      → Hefty Effs (IO ⊤)
cat = {!!}
{-
do
  t <- putStrLn "Hello"
  ?
  -}

eTeletype :
        {Effs : Effect {lzero} {lzero}}
        → {{ IOEF Char ∈ Effs }}
        → {{ IOEF ⊤ ∈ Effs }}
        → Elaboration Teletype Effs
eTeletype {_} ⦃ w1 ⦄ ⦃ w2 ⦄ .alg (putChar x) fork k = ?
eTeletype {_} ⦃ w1 ⦄ ⦃ w2 ⦄ .alg getChar fork k = {!!}

Lift : Effect {lzero} {lzero} -> Effectᴴ {lzero} {lzero}
Opᴴ   (Lift x)   = Op x
Fork (Lift x) _  = Nil
Retᴴ  (Lift x)   = Ret x

eLift : {Effs E : Effect {lzero} {lzero} }
        → {{E  ∈ Effs }}
        -> Elaboration (Lift E) Effs
eLift ⦃ w ⦄ .alg op fork k =
  impure (inject w op) λ ret → k (project w ret)
   where open import Control.Effect.Algebraic.Effect.OpenUnion using (inject)


eAll : Elaboration (Teletype ⊕ᴴ Lift (IOEF Char) ⊕ᴴ Lift (IOEF ⊤)) (IOEF Char ⊕ IOEF ⊤ ⊕ Nil)
eAll = eTeletype ⊕ᴬ eLift ⊕ᴬ eLift


main : IO ⊤
main = un (givenHandle (hIO ⊤)
          (givenHandle (hIO Char )
          (elaborate eAll cat) tt) tt)
