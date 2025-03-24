module Example.Experimental.NamesForEffectStorage where

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

infixr 5 _⊕_
_⊕_
  : {ol or r : Level}
  → (effl : Effect {ol} {r})
  → (effr : Effect {or} {r})
  → Effect {(ol ⊔ or)} {r}
effl ⊕ effr = record
  { Op = Op effl ⊎ Op effr
  ; Ret = λ where
      (inl opl) → Ret effl opl
      (inr opr) → Ret effr opr
  }


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

infix 4 _∣_∈_
data _∣_∈_ {o r : Level}
  :  (Eff      : Effect {o} {r})
  -> (Effs\Eff : Effect {o} {r}) --Дополнение
  -> (Effs     : Effect {o} {r})
  -> Set (lsuc (o ⊔ r))
  where
    insert
      :  {x y : Effect {o} {r}}
      -> y ∣ x ∈ x ⊕ y
    sift
      :  {x y z y\x : Effect {o} {r}}
      -> y\x  ∣ x ∈ y
      -> z ⊕ y\x ∣ x ∈ z ⊕ y

inject2
  : {o r : Level}
  → {Eff Effs C : Effect {o} {r}}
  → (w : C ∣ Eff ∈ Effs )
  → (op : Op Eff)
  → Op Effs
inject2 insert op   = inl op
inject2 (sift w) op = inr (inject2 w op)

infix 4 effects_＝_∣_
data effects_＝_∣_{o r : Level}
  :  (Eff      : Effect {o} {r})
  -> (Effs\Eff : Effect {o} {r}) --Дополнение
  -> (Effs     : Effect {o} {r})
  -> Set (lsuc (o ⊔ r))
  where
    insert
      :  {x y : Effect {o} {r}}
      -> effects x ⊕ y ＝ x ∣ x ⊕ y
    sift
      :  {x y z y\x : Effect {o} {r}}
      -> effects y ＝ x ∣ y\x
      -> effects z ⊕ y ＝ x ∣ z ⊕ y\x

inject3
  : {o r : Level}
  → {Eff Effs C : Effect {o} {r}}
  → (w : effects Effs ＝ Eff ∣ C )
  → (op : Op Eff)
  → Op Effs
inject3 insert op   = inl op
inject3 (sift w) op = inr (inject3 w op)




infix 4 _and_∈_
data _and_∈_ {o r : Level}
  :  (Effs\Eff : Effect {o} {r}) --Compliment
  -> (Eff      : Effect {o} {r})
  -> (Effs     : Effect {o} {r})
  -> Set (lsuc (o ⊔ r))
  where
    insert
      :  {x y : Effect {o} {r}}
      -> x and y ∈ x ⊕ y
    sift
      :  {x y z y\x : Effect {o} {r}}
      -> x and y\x ∈ y
      -> x and z ⊕ y\x ∈ z ⊕ y

inject
  : {o r : Level}
  → {Eff Effs C : Effect {o} {r}}
  → (w : Eff and C ∈ Effs )
  → (op : Op Eff)
  → Op Effs
inject insert op   = inl op
inject (sift w) op = inr (inject w op)

project
  : {o r : Level}
  → {Eff Effs C : Effect {o} {r}}
  → (w : Eff and C ∈ Effs )
  → {op : Op Eff}
  → (ret : Ret Effs (inject w op))
  → Ret Eff op
project insert ret   = ret
project (sift w) ret = project w ret


{-
send
  : {o r : Level}
  -> {Eff Effs C : Effect {o} {r}}
  -> ⦃ Eff∈Effs : Eff & C ∈ Effs  ⦄
  -> (op : Op Eff)
  -> Free Effs (Ret Eff op)
send ⦃ Eff∈Effs = Eff∈Effs ⦄ op = impure (inject Eff∈Effs op) λ ret → pure (project Eff∈Effs ret)

-}
{-
instance

  Effect-∈-inl
    :  {o r : Level }
    -> {Eff Effs C : Effect {o} {r}}
    -> Eff ∈ (Eff |> Effs) & Effs
  Effect-∈-inl = insert
  {-# OVERLAPS Effect-∈-inl #-}

  Effect-∈-inr
    :  {o r : Level }
    -> {x y z y\x  : Effect {o} {r}}
    -> ⦃ x ∈ y       &      y\x ⦄
    -> x ∈ z |> y    & z |> y\x
  Effect-∈-inr ⦃ Eff∈Effs ⦄ = sift Eff∈Effs
  {-# OVERLAPS Effect-∈-inr #-}



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

givenHandle : {a b : Level}
            {A : Set b}
            {B : Set b}
            {P : Set b}
            -> {X Effs Reduct : Effect {a} {b}}
            -> {{ X  ∈ Effs & Reduct  }}
            -> Handler A X P B Reduct
            -> Free (Effs) A
            -> (P -> Free {a} {b} Reduct B)
givenHandle h eff = fold (ret h) func (to-front eff) where
  to-front : _
  to-front = ?
  func : _
  func = ?
  --func (inl op) k p = hdl h op k p
  --func (inr op) k p = impure op λ x → k x p

putStrLn :
          {Effs C : Effect {lsuc lzero} {lzero}}
          -> {{Teletype ∈ Effs & C}}
          -> String
          -> Free Effs ⊤
putStrLn x = f (primStringToList x) where
  f : {Effs C : Effect} -> {{Teletype ∈ Effs & C}} -> List Char -> Free Effs ⊤
  f [] = send $ putChar '\n'
  f (x ∷ str) = do
    send $ putChar x
    f str

execAlgebra : Alg IOEF (IO A)
execAlgebra (liftIO ty f) k = f >>=IO k

exec : Free IOEF A -> IO A
exec = fold return execAlgebra


hFilesystem : Handler A Filesystem  ⊤ ( ⊤ ) IOEF
hFilesystem .ret _ _ = pure tt
hFilesystem .hdl (ReadFile path) k _            = impure (liftIO String (readFileIO path)) \ str -> (k str tt )
hFilesystem .hdl (WriteFile path text) k _      = impure (liftIO ⊤ (writeFileIO path text)) λ x → k tt tt

hTeletype : {Effs : Effect} -> Handler A Teletype ⊤ ( ⊤ ) (Effs |> IOEF)
hTeletype .ret _ _ = pure tt
hTeletype .hdl (putChar ch) k _ = impure (liftIO ⊤ (putCharIO ch)) (k tt )
hTeletype .hdl getChar k _      = impure (liftIO Char (getCharIO)) \ ch -> k ch tt

cat
  : {Effs C1 C2 : Effect {lsuc lzero} {lzero}}
  -> {{ Teletype   ∈ Effs & C1}}
  -> {{ Filesystem ∈ Effs & C2}}
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


-}
