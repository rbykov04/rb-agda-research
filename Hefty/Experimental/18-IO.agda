module Experimental.18-IO
    where

open import Agda.Builtin.IO
open import Agda.Builtin.Unit
open import Agda.Builtin.Nat
open import Agda.Builtin.Bool
open import Agda.Builtin.Sigma
open import Agda.Builtin.String
open import Agda.Builtin.Char
open import Agda.Builtin.List
open import Agda.Primitive
open import Agda.Builtin.Equality
open import Foundation.Base

open import Control.Effect.Algebraic.Effect
open import Control.Effect.Algebraic.Hefty hiding (_>>=_; _>>_)
open import Control.Effect.Algebraic.Hefty.RowInsert hiding (inject)
open import Control.Effect.Algebraic.Hefty hiding (_>>=_; _>>_)
open import Control.Effect.Algebraic.Effect.Free hiding (_>>=_; _>>_)
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
IOEF A .Ret x = A


execAlgebra : Alg (IOEF A) (IO B)
execAlgebra op k = op >>=IO k

exec : Free (IOEF A) A → IO A
exec = Control.Effect.Algebraic.Effect.Free.fold return execAlgebra

exec1 : Free (IOEF A) (IO A) → IO A
exec1 = Control.Effect.Algebraic.Effect.Free.fold id execAlgebra

runIO : Free ( IOEF A ⊕ IOEF B ) B → IO B
runIO = Control.Effect.Algebraic.Effect.Free.fold return func
  where
  func : _
  func (inl op) k = op >>=IO k
  func (inr op) k = op >>=IO k



program : {Effs : Effect {lzero} {lzero} }
      → {{IOEF ⊤ ∈ Effs }}
      → Free Effs ⊤
program = do
  send (putCharIO 'h')
  send (putCharIO 'e')
  send (putCharIO 'l')
  send (putCharIO 'l')
  send (putCharIO 'o')
  send (putCharIO '\n')
  where open import Control.Effect.Algebraic.Effect.Free using (_>>=_; _>>_)


program1 : {Effs : Effect {lzero} {lzero} }
          → {{IOEF Char ∈ Effs }}
          → {{IOEF ⊤ ∈ Effs }}
          → Free Effs ⊤
program1 = do
  send (putCharIO 'h')
  send (putCharIO 'e')
  send (putCharIO 'l')
  send (putCharIO 'l')
  send (putCharIO 'o')
  send (putCharIO '\n')
  a <- send (getCharIO)
  send (putCharIO a)
  send (putCharIO a)
  send (putCharIO a)
  send (putCharIO a)
  where open import Control.Effect.Algebraic.Effect.Free using (_>>=_; _>>_)

main1 : IO ⊤
main1 = (runIO program1)


Nil : Effect {lzero} {lzero}
Op  Nil = ⊥
Ret Nil = λ ()


un : Free Nil A -> A
un (pure x) = x

data LiftIOOP  : Set1 where
  liftIO : ( A : Set) → IO A → LiftIOOP

data One : Set1 where
 one : One

LiftIO :  Effectᴴ {lsuc lzero} {lzero} {lzero}
LiftIO .Opᴴ = LiftIOOP
LiftIO .Fork (liftIO A x) = record
  { Op = ⊤
  ; Ret = λ _ → IO A }
LiftIO .Retᴴ (liftIO A x) = A


`liftIO : {H H' : Effectᴴ}
      → {{heftyrow H ＝ LiftIO ∣ H'}}
      → {A : Set}
      → IO A
      → Hefty H A
`liftIO {H} {H'} ⦃ w ⦄ {A} io =
  impure (inject ⦃ w ⦄ (liftIO A io))
        (proj-fork-l {{w}} (liftIO A io) λ b → pure io)
        \ ret → pure ((proj-ret-l {{w}} ret))
    where open import Control.Effect.Algebraic.Hefty.RowInsert using (inject)


Elaboration1 :
    Effectᴴ {lsuc lzero} {lzero} {lzero}
    -> Effect {lzero} {lzero}
    -> Set (lsuc (lsuc lzero))
Elaboration1 H Eff = Algᴴ H (Free Eff)



eLiftIO :
        {Effs : Effect {lzero} {lzero}}
        → {{ IOEF Char ∈ Effs }}
        → {{ IOEF ⊤ ∈ Effs }}
        → Elaboration1 LiftIO Effs
eLiftIO .alg (liftIO A op) fork k = do
  x <- impure {!!} {!!}
  k {!!}
  where open import Control.Effect.Algebraic.Effect.Free using (_>>=_; _>>_)


program2 : {H H' : Effectᴴ}
          → {{heftyrow H ＝ LiftIO ∣ H'}}
          → Hefty H ⊤
program2 = do
    `liftIO (putCharIO 'h')
    `liftIO (putCharIO 'e')
    `liftIO (putCharIO 'l')
    `liftIO (putCharIO 'l')
    `liftIO (putCharIO 'o')
    a <- `liftIO getCharIO
    `liftIO (putCharIO a)
    `liftIO (putCharIO a)
    `liftIO (putCharIO a)

    where open import Control.Effect.Algebraic.Hefty using (_>>=_; _>>_)


