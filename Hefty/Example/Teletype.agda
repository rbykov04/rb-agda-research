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

open import Effect.Core.Free hiding (Handler)
--hiding (_>>=_ ; _>>_)
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





{-
fold2 pure' alg (pure x) = pure' x
fold2 pure' alg (impure op k) with alg op
... | imp = imp \ x -> (fold2 pure' alg) (k x)
-}


record Handler2 (A : Set) (E : Effect) (P : Set) (B : Set) (Continue : Effect) : Set₁ where
    field ret : A -> IO (P -> Free Continue B)
          hdl : Alg2 E (P -> Free Continue B)
open Handler2 public

-- it is like Exec Teletype in Data Type La Carte
hTeletype : {Eff : Effect} -> Handler2 A Teletype ⊤ (IO ⊤) Eff
hTeletype .ret = {!!}
-- pure $ return tt
hTeletype .hdl (putChar ch) k = putCharIO ch >>> k tt
hTeletype .hdl getChar f      = getCharIO >>>= f



fold2 : (A -> B) -> Alg2 Eff B -> Free Eff A -> B
fold2 pure' alg  = {!!}


-- like in Data Type La Carte
exec :
            {A B P : Set}
            -> {Eff Here There : Effect}
            -> {{ EffectStorage Eff Here There  }}
            -> Handler2 A Here P B There
            -> Free Eff A
            -> (P -> Free There B)
exec {A} {B} {P} {E} {Here} {There} h eff =
  fold2 {!!} func (to-front eff) where
    func : Alg2 (coProduct Here There) (P -> Free There B)
    func (injl x) k = h .hdl x k
    func (injr y) k = {!!}
    {-
    func (injl op) k with h .hdl op
    func (injl op) k with h .hdl op
    ... | q = q {!!}
    func (injr op) k = {!!}
    --return (impure op k)
    -- return \ p -> impure op \ x -> {!!}
    --return {!impure ? ?!}
   -- impure op \ x -> {!!}
    -- impure op \ x -> {!!}
    --impure ? ?
-}

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

main : IO ⊤
main = un ((exec hTeletype program) tt)
