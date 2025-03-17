{-# OPTIONS  --backtracking-instance-search  #-}
module Example.IO where

open import Agda.Builtin.Unit
open import Agda.Builtin.Sigma
open import Agda.Builtin.List
open import Agda.Builtin.Char
open import Agda.Builtin.String
open import Agda.Builtin.IO
open import Agda.Builtin.Equality
open import Agda.Primitive

open import Mystdlib.Mystdlib

open import Effect.Core.Free hiding ( _>>=_ ; _>>_ )
open import Effect.Core.Free2
open import Effect.Free2.IO hiding (return; _>>_; _>>=_)
open import Effect.Free2.State
open import Effect.Free2.Teletype
open import Effect.Free2.Filesystem

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
    _>>>=_  : IO A → (A → IO B) → IO B
{-# FOREIGN GHC import qualified Data.Text as T #-}
{-# FOREIGN GHC import qualified System.IO as SIO #-}
{-# COMPILE GHC return = \_ _ -> return    #-}
{-# COMPILE GHC _>>>=_  = \_ _ _ _ -> (>>=) #-}

infixl 1 _>>>_
_>>>_ : IO A → IO B → IO B
a >>> b = a >>>= λ _ → b



program1 : Free2 IOEF ⊤
program1 = impure (liftIO Char getCharIO) \ x ->
           impure (liftIO Char getCharIO) \ y ->
           impure (liftIO ⊤ (putCharIO y)) \ _ ->
           impure (liftIO ⊤ (putCharIO y)) \ _ ->
           impure (liftIO ⊤ (putCharIO y)) \ _ ->
           impure (liftIO ⊤ (putCharIO y)) \ _ ->
           impure (liftIO ⊤ (putCharIO y)) \ _ ->
           impure (liftIO ⊤ (putCharIO y)) \ _ ->
           pure tt



main1 : IO ⊤
main1 = exec2 program1

putStrLn : {E Here : Effect2}
          -> {{ EffectStorage2 E Here IOEF }}
          -> String
          -> Free2 E ⊤
putStrLn x = f (primStringToList x) where
  f : List Char
    -> {E Here : Effect2}
    -> {{ EffectStorage2 E Here IOEF }}
    -> Free2 E ⊤
  f [] =  `liftIO (putCharIO '\n') -- `putChar '\n'
  f (x ∷ str) = do
    `liftIO (putCharIO x) -- `putChar x
    f str

program : Free2 (coProduct2 State IOEF) ⊤
program = do
    putStrLn "Check def"
    def <- `get
    `liftIO (putCharIO def)
    `put 'a'
    a   <- `get
    putStrLn "\nCheck State"
    `liftIO (putCharIO a)
    putStrLn "\n"
    h1  <- `liftIO (getCharIO)
    `liftIO (putCharIO h1)
    `liftIO (putCharIO h1)
    `liftIO (putCharIO h1)
    `liftIO (putCharIO h1)
    putStrLn "Put2"
    h2  <- `liftIO (getCharIO)
    `liftIO (putCharIO h2)
    `liftIO (putCharIO h2)
    `liftIO (putCharIO h2)
    `liftIO (putCharIO h2)
    putStrLn "Put3"

main2 : IO ⊤
main2 = exec2 (givenHandle2 hSt program 'z') >>>= \ x -> return tt



program2 : Free2 (coProduct2 Teletype IOEF) ⊤
program2 = do
    `liftIO (putCharIO 'h')
    `liftIO (putCharIO 'e')
    `liftIO (putCharIO 'l')
    `liftIO (putCharIO 'l')
    `liftIO (putCharIO 'l')
    `liftIO (putCharIO '0')
    `liftIO (putCharIO '\n')
    `putChar 'h'
    `putChar 'e'
    `putChar 'l'
    `putChar 'l'
    `putChar 'o'
    `putChar '\n'
    ch <- `getChar
    ch2 <- `getChar
    `liftIO (putCharIO ch)
    `liftIO (putCharIO ch)
    `liftIO (putCharIO ch2)
    `liftIO (putCharIO ch2)

main3 : IO ⊤
main3 = exec2 (givenHandle2 hTeletype program2 tt) >>>= \ x -> return tt


putStrLn2 :
        {E There : Effect2}
          -> {{ EffectStorage2 E Teletype There }}
          -> String
          -> Free2 E ⊤
putStrLn2 x = f (primStringToList x) where
  f : List Char
    -> {E There : Effect2}
    -> {{ EffectStorage2 E Teletype There}}
    -> Free2 E ⊤
  f [] =  `putChar '\n'
  f (x ∷ str) = do
    `putChar x
    f str

program3 : Free2 (Filesystem |2> Teletype |2> IOEF) ⊤
program3 = do
  file <- readFile "test.txt"
  putStrLn2 file

main4 : IO ⊤
main4 = exec2 (givenHandle2 hFilesystem3
            (givenHandle2 hTeletype2 program3 tt) tt) >>>= \ x -> return tt

cat : {E There1 There2 : Effect2}
      -> {{ EffectStorage2 E Teletype   There1 }}
      -> {{ EffectStorage2 E Filesystem There2 }}
      -> String
      -> Free2 E ⊤
cat file = do
  file <- readFile file
  putStrLn2 file

program4 : Free2 (Filesystem |2> Teletype |2> IOEF) ⊤
program4 = do
  cat "test.txt"

main : IO ⊤
main = exec2 (givenHandle2 hTeletype
            (givenHandle2 hFilesystem program4 tt) tt) >>>= \ x -> return tt
