{-# OPTIONS  --backtracking-instance-search  #-}
module Effect.Free.Teletype where

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

hTeletype : {Eff : Effect} -> Handler2 A Teletype ⊤ ( IO ⊤ ) Eff
hTeletype .ret a x = pure (return x)
hTeletype .hdl (putChar ch) k = putCharIO ch >>> k tt
hTeletype .hdl getChar k      = getCharIO >>>= k


execAlgebra : Alg Teletype (IO A)
execAlgebra (putChar ch) k = putCharIO ch >>> k tt
execAlgebra getChar k      = getCharIO >>>= k

exec : Free Teletype A -> IO A
exec = fold return execAlgebra

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
