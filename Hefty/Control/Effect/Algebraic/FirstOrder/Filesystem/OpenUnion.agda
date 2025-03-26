module Control.Effect.Algebraic.FirstOrder.Filesystem.OpenUnion
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
open import Control.Effect.Algebraic.FirstOrder.Filesystem

private
  variable
    a b c d e : Level
    A : Set a
    B : Set b
    C : Set c
    D : Set d
    E : Set e


postulate
    readFileIO  : String -> IO String
    writeFileIO : String -> String -> IO ⊤
{-# FOREIGN GHC import qualified Data.Text as T #-}
{-# COMPILE GHC writeFileIO = \ path text -> writeFile (T.unpack path) (T.unpack text) #-}
{-# COMPILE GHC readFileIO = \ path ->  readFile (T.unpack path) >>= \ text -> return (T.pack text) #-}


hFilesystem
  : {Effs : Effect}
  -> {{ IOEF   ∈ Effs }}
  -> Handler A Filesystem  ⊤ ( ⊤ ) Effs
hFilesystem .ret _ _ = pure tt
hFilesystem .hdl (readFile path) k _ = do
  str <- send (liftIO String (readFileIO path))
  k str tt
hFilesystem .hdl (writeFile path text) k _ = do
  send (liftIO ⊤ (writeFileIO path text))
  k tt tt
