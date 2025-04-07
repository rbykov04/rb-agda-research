module Example.CLang.NonDet
    where



open import Agda.Builtin.Char
open import Agda.Builtin.Unit
open import Agda.Builtin.String
open import Agda.Builtin.Bool
open import Agda.Builtin.Nat
open import Agda.Builtin.List
open import Agda.Builtin.Maybe
open import Agda.Builtin.Sigma
open import Agda.Builtin.Equality

open import Foundation.Base
open import Data.String.Base
open import Data.Vec.Base

open import Control.Effect.Algebraic.FirstOrder.Nil
open import Control.Effect.Algebraic.FirstOrder.State
open import Control.Effect.Algebraic.FirstOrder.Throw
open import Control.Effect.Algebraic.Effect
open import Control.Effect.Algebraic.Effect.Free
open import Control.Effect.Algebraic.Effect.RowInsert

private
  variable
    a b c d e : Level
    A : Set a
    B : Set b
    C : Set c
    D : Set d
    E : Set e



data ChooseOp ( A : Set) : Set1
  where
  choose : List A → ChooseOp A

Choose : (A : Set) → FirstEffect
Choose A = record
  { Op = ChooseOp A
  ; Ret = λ where
    (choose _) -> A
  }

hChoose : {Effs : Effect} -> Handler A (Choose Char) ⊤ (List A) Effs
hChoose .ret x _ = pure (x ∷ [])
hChoose .hdl (choose []) k op = pure []
hChoose .hdl (choose (n ∷ ns)) k op = do
  x <- k n op
  y <- hChoose .hdl (choose ns) k op
  pure $ appendList x y
