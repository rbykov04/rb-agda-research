module Example.Output.Output where

open import Agda.Builtin.Sigma
open import Agda.Builtin.Unit
open import Agda.Builtin.String
open import Agda.Builtin.Nat
open import Agda.Builtin.Equality

open import Mystdlib.Universe
open import Foundation.Base

open import Control.Effect.Algebraic.Effect
open import Control.Effect.Algebraic.Effect.Free
open import Control.Effect.Algebraic.Effect.OpenUnion
open import Control.Effect.Algebraic.Effect.OpenUnion.Properties

open import Control.Effect.Algebraic.FirstOrder.IO hiding (_>>_ ; _>>=_)
open import Control.Effect.Algebraic.FirstOrder.Output
open import Control.Effect.Algebraic.FirstOrder.Output.OpenUnion
open import Control.Effect.Algebraic.FirstOrder.Nil
open import Control.Effect.Algebraic.FirstOrder.State
open import Control.Effect.Algebraic.FirstOrder.State.OpenUnion
open import Control.Effect.Algebraic.FirstOrder.Teletype
open import Control.Effect.Algebraic.FirstOrder.Teletype.OpenUnion


example1 : Free Output ⊤
example1 = impure (out "str") λ x → pure tt

hello : {Effs : Effect}
  → {{ Output ∈ Effs }}
  → Free Effs ⊤
hello = do
    send $ out "Hello"
    send $ out " "
    send $ out "world"
    send $ out "!"


test-incr :
    un ((givenHandle hOut hello)  tt) ≡ ("Hello world!" , tt)
test-incr = refl
