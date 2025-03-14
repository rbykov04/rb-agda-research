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

-- How does it work?
Alg2 : (Eff : Effect) -> (A : Set) -> Set
Alg2 Eff A = (op : Op Eff)(k : Ret Eff op -> (IO A)) -> IO A


record Handler2 (A : Set) (E : Effect) (P : Set) (B : Set) (Continue : Effect) : Set₁ where
    field ret : A -> P -> Free Continue B
          hdl : Alg2 E (P -> Free Continue B)
open Handler2 public

--Handler2 == Handler3

record Handler3 (A : Set) (E : Effect) (P : Set) (B : Set) (Continue : Effect) : Set₁ where
    field ret : A -> P -> Free Continue B
          hdl : Alg E (IO (P -> Free Continue B))
open Handler3 public

record Handler4 (A : Set) (E : Effect) (P : Set) (B : Set) (Continue : Effect) : Set₁ where
    field ret : A -> IO(P -> Free Continue B)
          hdl : Alg E (IO (P -> Free Continue B))
open Handler4 public




hTeletype : {Eff : Effect} -> Handler2 A Teletype ⊤ ( IO ⊤ ) Eff
hTeletype .ret a x = pure (return x)
hTeletype .hdl (putChar ch) k = putCharIO ch >>> k tt
hTeletype .hdl getChar k      = getCharIO >>>= k


execAlgebra : Alg Teletype (IO A)
execAlgebra (putChar ch) k = putCharIO ch >>> k tt
execAlgebra getChar k      = getCharIO >>>= k

exec1 : Free Teletype A -> IO A
exec1 = fold return execAlgebra

putStrLn1 : String -> Free Teletype ⊤
putStrLn1 x = f (primStringToList x) where
  f : List Char ->  Free Teletype ⊤
  f [] = impure (putChar '\n') \ _ -> pure tt
  f (x ∷ str) = impure (putChar x) \ _ -> f str

program1 : Free Teletype ⊤
program1 =
          impure (putChar 'H')              \ _ ->
          impure (putChar 'E')              \ _ ->
          impure (putChar 'L')              \ _ ->
          impure (putChar 'L')              \ _ ->
          impure (putChar 'L')              \ _ ->
          impure (putChar 'O')              \ _ ->
          impure (putChar '\n')             \ _ ->
          impure getChar                    \ a ->
          impure getChar                    \ b ->
          impure getChar                    \ c ->
          impure getChar                    \ d ->
          impure (putChar 'a')              \ _ ->
          impure (putChar '=')              \ _ ->
          impure (putChar a)                \ _ ->
          impure (putChar '\n')             \ _ ->
          impure (putChar 'b')              \ _ ->
          impure (putChar '=')              \ _ ->
          impure (putChar b)                \ _ ->
          impure (putChar '\n')             \ _ ->
          impure (putChar 'c')              \ _ ->
          impure (putChar '=')              \ _ ->
          impure (putChar c)                \ _ ->
          impure (putChar '\n')             \ _ ->
          impure (putChar 'd')              \ _ ->
          impure (putChar '=')              \ _ ->
          impure (putChar d)                \ _ ->
          impure (putChar '\n')             \ _ ->
          impure (putChar 'E')              \ _ ->
          impure (putChar 'N')              \ _ ->
          impure (putChar 'D')              \ _ ->
          impure (putChar '\n')             \ _ ->
          pure tt


``putChar : {Eff : Effect} -> Char -> Free (coProduct Eff Teletype) ⊤
``putChar ch = impure (injr (putChar ch)) \ x -> pure x

``getChar : {Eff : Effect} -> Free (coProduct Eff Teletype) Char
``getChar = impure (injr (getChar)) \ x -> pure x

putStrLn : {Eff : Effect} -> String -> Free (coProduct Eff Teletype) ⊤
putStrLn x = f (primStringToList x) where
  f : List Char ->  Free (coProduct Eff Teletype) ⊤
  f [] =   ``putChar '\n'
  f (x ∷ str) = do
    ``putChar x
    f str



main1 : IO ⊤
main1 = exec1 program1


program : Free (coProduct State Teletype) ⊤
program = do
    putStrLn "Check def"
    def <- `get
    ``putChar def
    `put 'a'
    a <- `get
    putStrLn "\nCheck State"
    ``putChar a
    putStrLn "\n"
    h1 <- ``getChar
    ``putChar h1
    ``putChar h1
    ``putChar h1
    putStrLn "Put2"
    h2 <- ``getChar
    ``putChar h2
    putStrLn "Put3"



main : IO ⊤
main = exec1 (givenHandle hSt program 'z') >>>= \ x -> return tt
