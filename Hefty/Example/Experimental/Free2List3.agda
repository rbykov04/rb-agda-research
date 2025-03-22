{- Inspired (copied) from V.Lozovoy -}
{-# OPTIONS  --backtracking-instance-search  #-}
module Example.Experimental.Free2List3 where

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

open import Mystdlib.Mystdlib

open import Effect.Core.Free2 using (Effect2 ;  _|2>_ ; _⦊_)
open import Effect.Free2.Teletype using (Teletype ; TeletypeOp ; getCharIO ; putCharIO ; putChar)
open import Effect.Free2.IO using (IOEF ; return; liftIO )
open import Effect.Free2.Filesystem using (Filesystem ; FileSystemOp ; ReadFile)

private
  variable
    a b c d e : Level
    A : Set a
    B : Set b
    C : Set c
    D : Set d
    E : Set e


-- Специализированный для эффекта список
-- TODO: когда будут обычные списки, использовать их
data Row (o r : Level) : Set (lsuc (o ⊔ r)) where
  [] : Row o r
  _∷_ : Effect2 {o} {r} → Row o r → Row o r

infixr 5 _∷_

data Op {o r : Level} : Row o r → Set (lsuc (o ⊔ r)) where
  _∷~
    : {eff : Effect2 {o} {r}}
    → {row : Row o r}
    → (op : Effect2.Op eff)
    → Op (eff ∷ row)
  -∷_ : {eff : Effect2 {o} {r}} {row : Row o r} → Op row → Op (eff ∷ row)

infix 6 _∷~
infix 5 -∷_

module Examples where

  data Two : Set where
    one two : Two

  data Tri : Set where
    one two three : Tri

  Eff0 : Effect2 {lzero} {lzero}
  Eff0 = ⊥  ⦊ λ ()

  Eff1 : Effect2
  Eff1 = ⊤  ⦊ λ tt → ⊥

  Eff2 : Effect2
  Eff2 = Two  ⦊ λ _ → ⊤

  Eff3 : Effect2
  Eff3 = Tri  ⦊ λ _ → ⊤


  {-
  -- У этой строки нет операций
  row : Row _ _
  row = []

  op : Op row
  op = ?
  -}

  {-
  -- У этой строки один эффект, но операций нет, так как у эффекта операций нет
  row0 : Row _ _
  row0 = Eff0 ∷ []

  op0 : Op row0
  op0 = ? ∷~
  -}

  -- У этой строки одна операция
  row1 : Row _ _
  row1 = Eff1 ∷ []

  op1-0 : Op row1
  op1-0 = tt ∷~

  -- У этой строки два эффекта и три операции
  row2 : Row _ _
  row2 = Eff1 ∷ Eff2 ∷ []

  op2-0 : Op row2
  op2-0 = tt ∷~

  op2-1-0 : Op row2
  op2-1-0 = -∷ one ∷~

  op2-1-1 : Op row2
  op2-1-1 = -∷ two ∷~

  -- У этой строки три эффекта и шесть операций
  row3 : Row _ _
  row3 = Eff1 ∷ Eff2 ∷ Eff3 ∷ []

  op3-0 : Op row3
  op3-0 = tt ∷~

  op3-1-0 : Op row3
  op3-1-0 = -∷ one ∷~

  op3-1-1 : Op row3
  op3-1-1 = -∷ two ∷~

  op3-2-0 : Op row3
  op3-2-0 = -∷ -∷ one ∷~

  op3-2-1 : Op row3
  op3-2-1 = -∷ -∷ two ∷~

  op3-2-2 : Op row3
  op3-2-2 = -∷ -∷ three ∷~

  -- У этой строки тоже три эффекта и шесть операций
  row4 : Row _ _
  row4 = Eff3 ∷ Eff2 ∷ Eff1 ∷ []

  op4-0-0 : Op row4
  op4-0-0 = one ∷~

  op4-0-1 : Op row4
  op4-0-1 = two ∷~

  op4-0-2 : Op row4
  op4-0-2 = three ∷~


  op4-1-0 : Op row4
  op4-1-0 = -∷ one ∷~

  op4-1-1 : Op row4
  op4-1-1 = -∷ two ∷~

  op4-2 : Op row4
  op4-2 = -∷ -∷ tt ∷~

Ret
  : {o r : Level}
  → (row : Row o r)
  → (Op row)
  → Set r
Ret [] ()
Ret (eff ∷ effs) (op ∷~) = Effect2.Ret eff op
Ret (eff ∷ effs) (-∷ ops) = Ret effs ops

data Free {o r a : Level} (Effs : Row o r) (A : Set a) : Set (lsuc (o ⊔ r ⊔ a)) where
  pure
    : (a : A)
    → Free Effs A
  impure
    : (op : Op Effs)
    → (k : Ret Effs op → Free Effs A)
    → Free Effs A

Alg
  : {o r a : Level}
  → (Effs : Row o r)
  → (A : Set a)
  → Set (lsuc o ⊔ lsuc r ⊔ a)
Alg Effs A = (op : Op Effs) → (k : Ret Effs op → A) → A

fold
  : {o r a b : Level}
  → {Effs : Row o r} {A : Set a} {B : Set b}
  → (A → B)
  → (Alg Effs B)
  → Free Effs A
  → B
fold point alg (pure a) = point a
fold point alg (impure op k) = alg op (λ r → fold point alg (k r))



_>>=_ : {a b : Level} {A : Set b} {B : Set b}
        {Effs : Row a b}
        -> Free Effs A -> (A -> Free Effs B) -> Free Effs B
m >>= g = fold g impure m

-- How does it work?
_>>_ : {a b : Level} {A : Set b} {B : Set b}
       {Effs : Row a b}
       -> Free Effs A → Free Effs B → Free Effs B
m1 >> m2 = m1 >>= λ _ → m2

{-
data Any {a b : Level}
         (P : Effect2 {a} {b} → Set (lsuc (a ⊔ b))) : List (Effect2 {a} {b}) → Set (lsuc (a ⊔ b)) where
  here  : ∀ {x : Effect2} {xs : List Effect2} → P x → Any P (x ∷ xs)
  there : ∀ {x : Effect2} {xs : List Effect2} → Any P xs → Any P (x ∷ xs)

infix 4 _∈_
-}
{-
record Effect (o r : Level) : Type (ℓsuc (o ⊔ r)) where
  constructor __
  field
    Op : Type o
    Ret : Op → Type r

infix 6 _⦊_

_∈_ :{a b : Level}
      (x : Effect2 {a} {b})
      -> (Effs : Row a b)
      -> {!Set!}
x ∈ xs = (Op ? , Ret ?)

send : {a b : Level} {E Here There : Effect2 {a} {b}}
       {Effs : Row a b}
     -> ⦃ Here ∈ Effs ⦄
     -> (op : Effect2.Op Here)
     -> Free Effs (Effect2.Ret Here op)

send = ?
-}
{-
{Effs = _} ⦃ op ∷~ ⦄ x = impure (op ∷~) \ o → pure  {!!}
send {Effs = _} ⦃ op ∷~ ⦄ x = impure (op ∷~) \ o → pure  {!!}
send {Effs = _} ⦃ -∷ w ⦄ x = impure {!!} {!!}
-}

_ : Free (Teletype ∷ Filesystem ∷ []) ⊤
_
  = impure (-∷ ReadFile "test.txt" ∷~) \ file
  -> impure (putChar '\n' ∷~) λ tt
  -> pure tt




{-
_
  : {Effs : Row lzero lzero}
  → ⦃ Teletype ∈ Effs ⦄
  → ⦃ Filesystem ∈ Effs ⦄
  → Free Effs ⊤
_ = do
  ?
-}
{-
  send ask
  send (modify λ x → x)
-}
