{-# OPTIONS  --backtracking-instance-search  #-}
module Example.Experim where

open import Agda.Builtin.Unit
open import Agda.Builtin.Sigma
open import Agda.Builtin.List
open import Agda.Builtin.Char
open import Agda.Builtin.String
open import Agda.Builtin.IO
open import Agda.Primitive

open import Mystdlib.Mystdlib

open import Effect.Core.Free hiding (Handler)
open import Effect.Free.Output
open import Effect.Free.Nil

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

          --Alg2 :: ((op : Op Eff)(k : Ret Eff op -> (IO ⊤)) -> IO ⊤)
foldTerm1 : (A -> IO B)
            -> Alg Eff (IO B)
            -> Free Eff A -> IO B
foldTerm1 pur impur (pure x)      = pur x
foldTerm1 pur impur (impure op k) = impur op \ x -> foldTerm1 pur impur (k x)

foldTerm : (A -> IO B)
            -> Alg Eff (IO B)
            -> Free Eff A -> IO B
foldTerm = fold

record Handler2 (A : Set) (E : Effect) (P : Set) (B : Set) (Continue : Effect) : Set₁ where
    field ret : A -> P -> Free Continue B
          hdl : Alg2 E (P -> Free Continue B)
open Handler2 public



-- like in Data Type La Carte
{-
exec :
            {A B P : Set}
            -> {E Here There : Effect}
            -> {{ EffectStorage E Here There  }}
            -> Handler2 A Here P B There
            -> Free E A
            -> (P -> Free There B)
exec {A} {B} {P} {E} {Here} {There} h eff = {!!}
    fold (ret h) func (to-front eff) where
    func : Alg (coProduct Here There) (P -> Free There B)
    func  (injl op) k p = hdl h op k p
    func (injr op) k p = impure op (λ x → k x p)
-}

hTeletype : {Eff : Effect} -> Handler2 A Teletype ⊤ ( IO ⊤ ) Eff
hTeletype .ret a x = pure (return x)
hTeletype .hdl (putChar ch) k = putCharIO ch >>> k tt
hTeletype .hdl getChar k      = getCharIO >>>= k


execAlgebra : Alg Teletype (IO ⊤)
execAlgebra (putChar ch) k = putCharIO ch >>> k tt
execAlgebra getChar k      = getCharIO >>>= k

exec1 : Free Teletype ⊤ -> IO ⊤
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


main : IO ⊤
main = exec1 program1

putStrLn : String -> Free (coProduct Teletype Nil) ⊤
putStrLn x = f (primStringToList x) where
  f : List Char ->  Free (coProduct Teletype Nil) ⊤
  f [] = `putChar '\n'
  f (x ∷ str) = do
    `putChar x
    f str


program : Free (coProduct Teletype Nil) ⊤
program = do
    putStrLn "Put"
    h1 <- `getChar
    `putChar h1
    `putChar h1
    `putChar h1
    putStrLn "Put2"
    h2 <- `getChar
    `putChar h2
    putStrLn "Put3"
{-
un2 : Free Nil A -> IO A
un2 (pure x) = {!!}
-}

{-
main1 : IO ⊤
main1 = un ((exec hTeletype program) tt)
-}
