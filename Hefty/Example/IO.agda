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
    readFileIO  : String -> IO String
    writeFileIO : String -> String -> IO ⊤
    return : A → IO A
    _>>>=_  : IO A → (A → IO B) → IO B
{-# FOREIGN GHC import qualified Data.Text as T #-}
{-# FOREIGN GHC import qualified System.IO as SIO #-}
{-# COMPILE GHC putCharIO = (SIO.hPutChar SIO.stderr) #-}
{-# COMPILE GHC getCharIO = SIO.getChar #-}
{-# COMPILE GHC writeFileIO = \ path text -> writeFile (T.unpack path) (T.unpack text) #-}
{-# COMPILE GHC readFileIO = \ path ->  readFile (T.unpack path) >>= \ text -> return (T.pack text) #-}
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

`liftIO :
      {E Here : Effect2 }
     -> {{ EffectStorage2 E Here IOEF}}
     -> {A : Set}
     -> (f : IO A)
     -> Free2 E A
`liftIO {{ w }} {A} f = impure (inj-insert-right2 (liftIO A f)) (\ x -> pure (proj-ret-right2 {{w}} x))

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

data StateOp : Set1 where
    get : StateOp
    put : Char -> StateOp

State : Effect2
Op  State = StateOp
Ret State get = Char
Ret State (put x) = ⊤

hSt : {Eff : Effect2} -> Handler2 A State Char ( A × Char ) Eff
ret hSt x s = pure (x , s)
hdl hSt get k n = k n n
hdl hSt (put m) k _ = k tt m


`put :
      {E There : Effect2}
     -> {{ EffectStorage2 E State There }}
     -> Char
     -> Free2 E ⊤
`put {{ w }} n = impure (inj-insert-left2 (put n) ) (λ x -> pure (proj-ret-left2 {{w}} x))

`get :
      {E There : Effect2}
     -> {{ EffectStorage2 E State There }}
     -> Free2 E Char
`get {{ w }}  = impure (inj-insert-left2 get ) (λ x -> pure (proj-ret-left2 {{w}} x))

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
