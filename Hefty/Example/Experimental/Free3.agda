{-
inspired: https://github.com/vasiliyl/cm-effects/blob/main/src/Control/Effect/Algebraic/Effect.agda
-}
module Example.Experimental.Free3 where

open import Agda.Builtin.Unit
open import Agda.Builtin.Nat
open import Agda.Builtin.Sigma
open import Agda.Builtin.List
open import Agda.Builtin.Char
open import Agda.Builtin.String
open import Agda.Builtin.IO
open import Agda.Builtin.Equality
open import Agda.Builtin.Reflection
open import Agda.Builtin.List
open import Agda.Primitive

open import Mystdlib.Mystdlib hiding (elim)

open import Effect.Core.Free2
  renaming
    (Effect2 to Effect
    )
  using
  ( Op
  ; Ret
  )

open import Effect.Free2.Teletype
  using
    ( Teletype
    ; TeletypeOp
    ; getCharIO
    ; putCharIO
    ; putChar
    ; getChar
    )
open import Effect.Free2.IO
  renaming
    ( _>>_ to _>>IO_
    ; _>>=_ to _>>=IO_
    )
  using
    ( IOEF
    ; return
    ; liftIO
    )
open import Effect.Free2.Filesystem
  using
  ( Filesystem
  ; ReadFile
  ; WriteFile
  ; writeFileIO
  ; readFileIO
  ; FileSystemOp
  )

private
  variable
    a b c d e : Level
    A : Set a
    B : Set b
    C : Set c
    D : Set d
    E : Set e

infixr 70 _⊎_
data _⊎_ {ℓa ℓb} (A : Set ℓa) (B : Set ℓb) : Set (ℓa ⊔ ℓb) where
  inl : A → A ⊎ B
  inr : B → A ⊎ B

elim : {ℓa ℓb : Level} {A : Set ℓa} {B : Set ℓb}
       {ℓ : Level} {C : A ⊎ B → Set ℓ}
       (f : (a : A) → C (inl a)) (g : (b : B) → C (inr b))
     → (s : A ⊎ B) → C s
elim f _ (inl x) = f x
elim _ g (inr x) = g x

_|>_
  : {ol or r : Level}
  → (effl : Effect {ol} {r})
  → (effr : Effect {or} {r})
  → Effect {(ol ⊔ or)} {r}
effl |> effr = record
  { Op = Op effl ⊎ Op effr
  ; Ret = λ where
      (inl opl) → Ret effl opl
      (inr opr) → Ret effr opr
  }

infixr 5 _|>_

data Free {o r ℓ : Level} (Eff : Effect {o} {r}) (A : Set ℓ) : Set (o ⊔ r ⊔ ℓ) where
  pure
    : (a : A)
    → Free Eff A
  impure
    : (op : Op Eff)
    → (k : Ret Eff op → Free Eff A)
    → Free Eff A

Alg
  : {o r a : Level}
  → (Eff : Effect {o} {r})
  → (A : Set a)
  → Set (o ⊔ r ⊔ a)
Alg Eff A = (op : Op Eff) → (k : Ret Eff op → A) → A

fold
  : {o r a b : Level}
  → {Eff : Effect {o} {r}} {A : Set a} {B : Set b}
  → (A → B)
  → (Alg Eff B)
  → Free Eff A
  → B
fold point alg (pure a) = point a
fold point alg (impure op k) = alg op (λ r → fold point alg (k r))

_>>=_
  : {o r a b : Level}
  → {Eff : Effect {o} {r}} {A : Set a} {B : Set b}
  → Free Eff A
  → (A → Free Eff B)
  → Free Eff B
f >>= g = fold g impure f

_>>_
  : {o r a b : Level}
  → {Eff : Effect {o} {r}} {A : Set a} {B : Set b}
  → Free Eff A
  → Free Eff B
  → Free Eff B
f >> g = f >>= λ _ → g

data _∈_ {o r : Level} : (Effect {o} {r}) -> (Effect {o} {r}) -> Set (lsuc (o ⊔ r)) where
   reflex
    :  {x  : Effect {o} {r}}
    -> x ∈ x
   insert
    :  {x  : Effect {o} {r}}
    -> {y : Effect {o} {r}}
    -> x ∈ (x |> y)
   sift
    :  {x  : Effect {o} {r}}
    -> {y : Effect {o} {r}}
    -> {z : Effect {o} {r}}
    -> x ∈ y
    -> x ∈ (z |> y)
infix 4 _∈_
instance
  Effect-∈-here
    :  {o r : Level }
    -> {Eff : Effect {o} {r}}
    -> Eff ∈ Eff
  Effect-∈-here = reflex
  {-# OVERLAPS Effect-∈-here #-}

  Effect-∈-inl
    :  {o r : Level }
    -> {Eff Effs : Effect {o} {r}}
    -> Eff ∈ Eff |> Effs
  Effect-∈-inl = insert 
  {-# OVERLAPS Effect-∈-inl #-}

  Effect-∈-inr
    :  {o r : Level }
    -> {Eff' Eff Effs : Effect {o} {r}}
    -> ⦃ Eff∈Effs : Eff ∈ Effs ⦄
    -> Eff ∈ Eff' |> Effs
  Effect-∈-inr ⦃ Eff∈Effs ⦄ = sift Eff∈Effs
  {-# OVERLAPS Effect-∈-inr #-}

inject
  : {o r : Level}
  → {Eff : Effect {o} {r}} {Effs : Effect {o} {r}}
  → (w : Eff ∈ Effs)
  → (op : Op Eff)
  → Op Effs
inject reflex x   = x
inject insert op   = inl op
inject (sift w) op = inr (inject w op)

project
  : {o r : Level}
  → {Eff : Effect {o} {r}} {Effs : Effect {o} {r}}
  → (w : Eff ∈ Effs)
  → {op : Op Eff}
  → (ret : Ret Effs (inject w op))
  → Ret Eff op
project reflex ret   = ret
project insert ret   = ret
project (sift w) ret = project w ret

send
  : {o r : Level}
  -> {Eff Effs : Effect {o} {r}}
  -> ⦃ Eff∈Effs : Eff ∈ Effs ⦄
  -> (op : Op Eff)
  -> Free Effs (Ret Eff op)
send ⦃ Eff∈Effs = Eff∈Effs ⦄ op = impure (inject Eff∈Effs op) λ ret → pure (project Eff∈Effs ret)


Alg2 : {a b : Level }
       (Eff : Effect {a} {b})
       -> (A : Set (lsuc a ⊔ lsuc b))
       -> Set (lsuc a ⊔ lsuc b)
Alg2 Eff A = (op : Op Eff)(k : Ret Eff op -> (A)) -> A

record Handler {o r a : Level}
                (A : Set a)
                (E : Effect {o} {r})
                (P : Set a)
                (B : Set a)
                (Continue : Effect {o} {r})
                : Set (lsuc (o ⊔ r ⊔ a))
                where
    field ret : A -> P -> Free Continue B
          hdl : Alg E (P -> Free Continue B)
open Handler public


{-
X ∈ Y + Z - we will ignore this case
Free (?) -> Free (?)
-}
givenHandle : {a b : Level}
            {A : Set b}
            {B : Set b}
            {P : Set b}
            -> {Effs     : Effect {a} {b}}
            -> {X        : Effect {a} {b}}
            -> Handler A X P B Effs
            -> Free (X |> Effs) A
            -> (P -> Free {a} {b} Effs B)
givenHandle h eff = fold (ret h) func eff where
  func : _
  func (inl op) k p = hdl h op k p
  func (inr op) k p = impure op λ x → k x p

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

execAlgebra : Alg IOEF (IO A)
execAlgebra (liftIO ty f) k = f >>=IO k

exec : Free IOEF A -> IO A
exec = fold return execAlgebra


hFilesystem
  : {Effs : Effect}
  -> {{ IOEF   ∈ Effs }}
  -> Handler A Filesystem  ⊤ ( ⊤ ) Effs
hFilesystem .ret _ _ = pure tt
hFilesystem .hdl (ReadFile path) k _ = do
  str <- send (liftIO String (readFileIO path))
  k str tt
hFilesystem .hdl (WriteFile path text) k _ = do
  send (liftIO ⊤ (writeFileIO path text))
  k tt tt

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


cat
  : {Effs : Effect {lsuc lzero} {lzero}}
  -> {{ Teletype   ∈ Effs }}
  -> {{ Filesystem ∈ Effs }}
  -> String
  -> Free Effs ⊤
cat file = do
  txt <- send $ ReadFile file
  putStrLn txt



program : Free (Filesystem |> Teletype |> IOEF) ⊤
program = do
  cat "test.txt"


program2 : Free (Teletype |> Filesystem |> IOEF) ⊤
program2 = do
  cat "test.txt"

main : IO ⊤
main = exec (givenHandle hTeletype
            (givenHandle hFilesystem program tt) tt) >>=IO \ x -> return tt

main1 : IO ⊤
main1 = exec (givenHandle hFilesystem
             (givenHandle hTeletype program2 tt) tt) >>=IO \ x -> return tt


givenHandle' : {a b : Level}
            {A : Set b}
            {B : Set b}
            {P : Set b}
            -> {Effs     : Effect {a} {b}}
            -> {X        : Effect {a} {b}}
            -> {E        : Effect {a} {b}}
            -> {{ w1 : X    ∈ E }}
            -> {{ w2 : Effs ∈ E }}
            -> Handler A X P B Effs
            -> Free E A
            -> (P -> Free {a} {b} Effs B)
givenHandle' {a} {b} {A} {B} {P} {Effs} {X} {E} ⦃ w1 ⦄ ⦃ w2 ⦄ h eff =
    fold (ret h) func (to-front eff) where
      to-front
            :  {{ w1 : X    ∈ E }}
            -> {{ w1 : Effs ∈ E }}
            -> Free E A -> Free (X |> Effs) A
      to-front ⦃ reflex ⦄ ⦃ reflex ⦄ (pure a) = pure a
      to-front ⦃ reflex ⦄ ⦃ reflex ⦄ (impure op k) = do
        x <- send op
        to-front {{reflex}} (k x)
      to-front ⦃ reflex ⦄ ⦃ insert ⦄ (pure a) = pure a
      to-front ⦃ reflex ⦄ ⦃ insert ⦄ (impure op k) = do
        x <- send op
        to-front {{reflex}} (k x)
      to-front ⦃ reflex ⦄ ⦃ sift w2 ⦄ (pure a) = pure a
      to-front ⦃ reflex ⦄ ⦃ sift w2 ⦄ (impure op k) = do
        x <- send op
        to-front {{reflex}} (k x)
      to-front ⦃ insert ⦄ ⦃ w2 ⦄ (pure a) = pure a
      to-front ⦃ insert ⦄ ⦃ w2 ⦄ (impure (inl x) k) = ?
      to-front ⦃ insert ⦄ ⦃ w2 ⦄ (impure (inr x) k) = ?
      to-front ⦃ sift w1 ⦄ ⦃ w2 ⦄ (pure a) = pure a
      to-front ⦃ sift w1 ⦄ ⦃ w2 ⦄ (impure op k) = {!!}
      func : _
      func (inl op) k p = hdl h op k p
      func (inr op) k p = impure op λ x → k x p



main3 : IO ⊤
main3 = exec (givenHandle' {{insert}} {{sift (sift reflex)}} hTeletype
            (givenHandle' {{sift insert}} {{reflex}} hFilesystem program2 tt) tt) >>=IO \ x -> return tt
