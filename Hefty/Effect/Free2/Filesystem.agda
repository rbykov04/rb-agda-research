{-# OPTIONS  --backtracking-instance-search  #-}
module Effect.Free2.Filesystem where

open import Agda.Builtin.Unit
open import Agda.Builtin.Sigma
open import Agda.Builtin.List
open import Agda.Builtin.Char
open import Agda.Builtin.String
open import Agda.Builtin.IO
open import Agda.Builtin.Equality
open import Agda.Primitive

open import Mystdlib.Mystdlib

open import Effect.Core.Free2
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
    readFileIO  : String -> IO String
    writeFileIO : String -> String -> IO ⊤
{-# FOREIGN GHC import qualified Data.Text as T #-}
{-# COMPILE GHC writeFileIO = \ path text -> writeFile (T.unpack path) (T.unpack text) #-}
{-# COMPILE GHC readFileIO = \ path ->  readFile (T.unpack path) >>= \ text -> return (T.pack text) #-}
data FileSystemOp : Set1 where
  ReadFile   : String -> FileSystemOp
  WriteFile  : String -> String -> FileSystemOp

Filesystem : Effect2
Filesystem .Op                        = FileSystemOp
Filesystem .Ret (ReadFile file)       = String
Filesystem .Ret (WriteFile file text) = ⊤



readFile :
      {E There : Effect2}
     -> {{ EffectStorage2 E Filesystem There}}
     -> String
     -> Free2 E String
readFile {{ w }} path = impure (inj-insert-left2 (ReadFile path)) (λ x -> pure (proj-ret-left2 {{w}} x))

writeFile :
      {E There : Effect2}
     -> {{ EffectStorage2 E Filesystem There}}
     -> String
     -> String
     -> Free2 E ⊤
writeFile {{ w }} path text =
  impure (inj-insert-left2 (WriteFile path text))
  (λ x -> pure (proj-ret-left2 {{w}} x))

hFilesystem2 :  {Eff : Effect2} -> Handler2 A Filesystem ⊤ ( ⊤ ) (Eff |2> IOEF)
hFilesystem2 .ret _ _ = pure tt
hFilesystem2 .hdl (ReadFile path) k _       =
  impure (injr (liftIO String (readFileIO path))) \ ch -> k ch tt
hFilesystem2 .hdl (WriteFile path text) k _ =
  impure (injr (liftIO ⊤ (writeFileIO path text))) (k tt )

hFilesystem :  {E Here : Effect2}
            -> {{ EffectStorage2 E Here IOEF}}
            -> Handler2 A Filesystem ⊤ ( ⊤ ) E
hFilesystem .ret _ _ = pure tt
hFilesystem {{w}} .hdl (ReadFile path) k oo       =
  impure
    (inj-insert-right2 {{w}}(liftIO String (readFileIO path)))
    \ ch -> k (proj-ret-right2 {{w}} ch) tt
hFilesystem {{w}} .hdl (WriteFile path text) k _ =
  impure
    (inj-insert-right2  (liftIO ⊤ (writeFileIO path text)))
    \ x -> k (proj-ret-right2 {{w}} x ) tt


hFilesystem3 : Handler2 A Filesystem ⊤ ( ⊤ ) IOEF
hFilesystem3 .ret _ _ = pure tt
hFilesystem3 .hdl (ReadFile path) k _            = impure (liftIO String (readFileIO path)) \ str -> (k str tt )
hFilesystem3 .hdl (WriteFile path text) k _      = impure (liftIO ⊤ (writeFileIO path text)) λ x → k tt tt
