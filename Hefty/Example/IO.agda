{-# OPTIONS  --backtracking-instance-search  #-}
module Example.IO where

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
open import Effect.Free.Throw
open import Effect.Free.Nil
open import Effect.Free.State Char

private
  variable
    a b c d e : Level
    A : Set a
    B : Set b
    C : Set c
    D : Set d
    E : Set e

record Effect2 {a b : Level} : Set (lsuc (a ⊔ b)) where -- (a ⊔ b) where
 field Op  : Set a
       Ret : Op -> Set b
open Effect2 public

data IOOP : Set1 where
  liftIO  : (A : Set) -> IO A ->  IOOP


IOEF : Effect2
IOEF .Op = IOOP
IOEF .Ret (liftIO ty x) = ty


data Free2 {a b : Level} (eff : Effect2 {a} {b}) ( A : Set b) : Set (lsuc (a ⊔ b)) where
    pure   : A                                                -> Free2 eff A
    impure : (op : Op eff) -> (k : Ret eff op -> Free2 eff A) -> Free2 eff A

data Sum2 {a : Level} (A : Set a) (B : Set a) : Set (lsuc (a)) where
  injl : (x : A) → Sum2 A B
  injr : (y : B) → Sum2 A B

elim2 :
        {a : Level}
        {C : Sum2 A B → Set (lsuc a)} →    -- it is a box
        ((x : A) → C (injl x)) → -- it is a function to convert left case to box
        ((x : B) → C (injr x)) → -- it is a function to convert right case to box
        (x : Sum2 A  B)             -- it is a what we can move to box
        → C x                     -- result
elim2 f g (injl x) = f x
elim2 f g (injr y) = g y


coProduct2 : {a b : Level} -> Effect2 {a} {b} -> Effect2 {a} {b} -> Effect2 {lsuc a} {b}
coProduct2 {a} {b} x y .Op = Sum2 {a} (Op x) (Op y)
coProduct2 {a} {b} x y .Ret (injl x1) = Ret x x1
coProduct2 {a} {b} x y .Ret (injr y1) = Ret y y1

infixr 12 _|2>_
_|2>_ : {a b : Level} -> Effect2 {a} {b} -> Effect2 {a} {b} -> Effect2 {lsuc a} {b}
_|2>_ = coProduct2

infixl 1 _>>>=_
postulate
    putCharIO : Char → IO ⊤
    getCharIO : IO Char
    return' : A → IO A
    _>>>=_  : IO A → (A → IO B) → IO B
{-# FOREIGN GHC import qualified Data.Text as T #-}
{-# FOREIGN GHC import qualified System.IO as SIO #-}
{-# COMPILE GHC putCharIO = (SIO.hPutChar SIO.stderr) #-}
{-# COMPILE GHC getCharIO = SIO.getChar #-}
{-# COMPILE GHC return' = \_ _ -> return    #-}
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

-- I am not sure about levels
Alg2 : {a b : Level }(Eff : Effect2 {a} {b}) -> (A : Set b) -> Set (a ⊔ b)
Alg2 Eff A = (op : Op Eff)(k : Ret Eff op -> (A)) -> A

fold2 : {a b : Level } {A : Set b} {B : Set b} {Eff : Effect2 {a} {b}}
        -> (A -> B)
        -> Alg2 Eff B
        -> Free2 {a} {b} Eff A
        -> B
fold2 g alg (pure x) = g x
fold2 g alg (impure op k) = alg op λ x -> fold2 g alg (k x)



execAlgebra2 : Alg2 IOEF (IO A)
execAlgebra2 (liftIO ty f) k = f >>>= k

exec2 : Free2 IOEF A -> IO A
exec2 = fold2 return' execAlgebra2
main : IO ⊤
main = exec2 program1


{-

`putChar :
      {E Here : Effect}
     -> {{ EffectStorage E Here Teletype }}
     -> Char
     -> Free E ⊤
`putChar {{ w }} ch = impure (inj-insert-right (putChar ch)) (λ x -> pure (proj-ret-right {{w}} x))

`getChar :
      {E Here : Effect}
     -> {{ EffectStorage E Here Teletype }}
     -> Free E Char
`getChar {{ w }} = impure (inj-insert-right getChar) (λ x -> pure (proj-ret-right {{w}} x))

putStrLn : {E Here : Effect}
          -> {{ EffectStorage E Here Teletype }}
          -> String
          -> Free E ⊤
putStrLn x = f (primStringToList x) where
  f : List Char
    -> {E Here : Effect}
    -> {{ EffectStorage E Here Teletype }}
    ->  Free E ⊤
  f [] =   `putChar '\n'
  f (x ∷ str) = do
    `putChar x
    f str
-}
{-
program : Free (coProduct State Teletype) ⊤
program = do
    putStrLn "Check def"
    def <- `get
    `putChar def
    `put 'a'
    a <- `get
    putStrLn "\nCheck State"
    `putChar a
    putStrLn "\n"
    h1 <- `getChar
    `putChar h1
    `putChar h1
    `putChar h1
    putStrLn "Put2"
    h2 <- `getChar
    `putChar h2
    putStrLn "Put3"

main : IO ⊤
main = execIO (givenHandle hSt program 'z') >>>= \ x -> return tt
-}

