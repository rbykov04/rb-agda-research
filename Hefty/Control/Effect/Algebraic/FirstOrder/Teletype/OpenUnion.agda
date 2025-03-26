module Control.Effect.Algebraic.FirstOrder.Teletype.OpenUnion
    where

open import Agda.Builtin.String
open import Agda.Builtin.Char
open import Agda.Builtin.List
open import Agda.Builtin.Unit
open import Agda.Builtin.IO

open import Foundation.Base

open import Control.Effect.Algebraic.Effect
open import Control.Effect.Algebraic.Effect.OpenUnion
open import Control.Effect.Algebraic.Effect.OpenUnion.Properties
open import Control.Effect.Algebraic.Effect.Free
open import Control.Effect.Algebraic.FirstOrder.IO hiding (_>>_ ; _>>=_)
open import Control.Effect.Algebraic.FirstOrder.Teletype

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

putStrLn :
          {Effs : Effect {lsuc lzero} {lzero}}
          -> {{Teletype ∈ Effs}}
          -> String
          -> Free Effs ⊤
putStrLn x = f (primStringToList x) where
  f : {Effs : Effect} -> {{Teletype ∈ Effs}} -> List Char -> Free Effs ⊤
  f [] = send $ putChar '\n'
  f (x ∷ str) = do
    send $ putChar x
    f str

hTeletype
  : {Effs : Effect}
  -> {{ IOEF   ∈ Effs }}
  -> Handler A Teletype  ⊤ ( ⊤ ) Effs
hTeletype .ret _ _ = pure tt
hTeletype .hdl (putChar ch) k _ = do
  send (liftIO ⊤ (putCharIO ch))
  k tt tt
hTeletype .hdl getChar k _      = do
  ch <- send (liftIO Char (getCharIO))
  k ch tt

