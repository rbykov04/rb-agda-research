{-# OPTIONS  --backtracking-instance-search  #-}
module Example.CLang.Tokenize
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
open import Control.Effect.Algebraic.Effect.Free hiding (_>>_ ; _>>=_)
open import Control.Effect.Algebraic.Effect.RowInsert
open import Control.Effect.Algebraic.Hefty hiding (_>>_ ; _>>=_)
open import Control.Effect.Algebraic.HighOrder.Lift
open import Control.Effect.Algebraic.HighOrder.Lift.RowInsert
open import Control.Effect.Algebraic.Hefty.RowInsert
open import Example.CLang.TokenTypes
open import Example.CLang.Effects
open import Example.CLang.NonDet

private
  variable
    a b c d e : Level
    A : Set a
    B : Set b
    C : Set c
    D : Set d
    E : Set e

tokenize1 : {H H1 H2 H3 H4 : Effectᴴ}
    → ⦃ heftyrow H ＝ (Lift TokenizerResult) ∣ H1 ⦄
    → ⦃ heftyrow H ＝ (Lift Logger) ∣ H2 ⦄
    → ⦃ heftyrow H ＝ (Lift TokenThrow) ∣ H3 ⦄
    → ⦃ heftyrow H ＝ Branch ∣ H4 ⦄
    → List Char
    → Parser
    → Hefty H ⊤
tokenize1 [] parser = do
    case finish (atok parser) (token (atok parser)) of λ where
        nothing          → pure tt
        (just tokenKind) → do
          up $ log ("add last token")
          up $ addToken (mkToken tokenKind 0 (pos parser))
    where open import Control.Effect.Algebraic.Hefty using (_>>=_ ; _>>_)
tokenize1 (ch ∷ text) parser =
    case build (atok parser) (token (atok parser)) ch of λ where
        nothing  → do
            up $ log ("build is fail, let's add to list")
            case finish (atok parser) (token (atok parser)) of λ where
                (just tokenKind) → do
                    up $ addToken (mkToken tokenKind 0 (pos parser))
                    newThread1 <- up branch
                    if newThread1
                        then (do
                                up $ log ("Parse " ++ show ch ++ " with NumParser")
                                case charToDigit ch of λ where
                                    (just d) → tokenize1 text (nextstep parser (mkANumber d))
                                    nothing → throwErrorᴴ (pos parser) ("invalid token: " ++ show ch)
                        ) else do
                            newThread2 <- up branch
                            if newThread2
                                then (do
                                        up $ log ("Parse " ++ show ch ++ " with WordParser")
                                        case charToWord ch of λ where
                                            (just symb) → do
                                                up $ log ("mkAWord" ++ show ch)
                                                tokenize1 text (nextstep parser (mkAWord symb))
                                            nothing → throwErrorᴴ (pos parser) ("invalid token: " ++ show ch)
                                ) else do
                                        up $ log ("Parse " ++ show ch ++ " with SpaceParser")
                                        case buildSpace space ch of λ where
                                            (just sp) → tokenize1 text (nextstep parser (mkASpace sp))
                                            nothing → throwErrorᴴ (pos parser) ("invalid token: " ++ show ch)
                nothing          → do
                    newThread1 <- up branch
                    if newThread1
                        then (do
                                up $ log ("Parse " ++ show ch ++ " with NumParser")
                                case charToDigit ch of λ where
                                    (just d) → tokenize1 text (nextstep parser (mkANumber d))
                                    nothing → throwErrorᴴ (pos parser) ("invalid token: " ++ show ch)
                        ) else do
                            newThread2 <- up branch
                            if newThread2
                                then (do
                                        up $ log ("Parse " ++ show ch ++ " with WordParser")
                                        case charToWord ch of λ where
                                            (just symb) → do
                                                up $ log ("mkAWord" ++ show ch)
                                                tokenize1 text (nextstep parser (mkAWord symb))
                                            nothing → throwErrorᴴ (pos parser) ("invalid token: " ++ show ch)
                                ) else do
                                        up $ log ("Parse " ++ show ch ++ " with SpaceParser")
                                        case buildSpace space ch of λ where
                                            (just sp) → tokenize1 text (nextstep parser (mkASpace sp))
                                            nothing → throwErrorᴴ (pos parser) ("invalid token: " ++ show ch)
        (just newATok) → do
            up $ log ("continue build '" ++ show ch ++ "'")
            tokenize1 text (record
                {pos = suc $ pos parser
                ; atok = record
                { tokenT = tokenT $ atok parser
                ; token  = newATok
                ; build  = build $ atok parser
                ; finish = finish $ atok parser } })
    where open import Control.Effect.Algebraic.Hefty using (_>>=_ ; _>>_)


tokenizeTextᴴ : {H H1 H2 H3 H4 : Effectᴴ}
    → ⦃ heftyrow H ＝ (Lift TokenizerResult) ∣ H1 ⦄
    → ⦃ heftyrow H ＝ (Lift Logger) ∣ H2 ⦄
    → ⦃ heftyrow H ＝ (Lift TokenThrow) ∣ H3 ⦄
    → ⦃ heftyrow H ＝ Branch ∣ H4 ⦄
   → String
    → Hefty H ⊤
tokenizeTextᴴ text = tokenize1 (toList text ) (mkParser 0 (mkASpace space))

eBranch2 : {Effs E1 : Effect}
    → ⦃ effrow Effs ＝ Logger ∣ E1 ⦄
    → Elaboration Branch Effs
eBranch2 .alg branch fork k = do

    send (log ("bla bla bla"))
    (l1 , x )  <- (# givenHandle hLogger (k true) tt)
    --(l2 , y )  <- (# givenHandle hLogger (k false) tt)
    send (log l1)
   -- eee2 <- k false
    k true
    where open import Control.Effect.Algebraic.Effect.Free using (_>>=_ ; _>>_)



eNil : {Eff : Effect} -> Elaboration (Lift Nil) Eff
alg eNil ()
eTokenizeElab : Elaboration
                    ( Branch
                    ⊕ᴴ Lift TokenizerResult
                    ⊕ᴴ Lift Logger
                    ⊕ᴴ Lift TokenThrow
                    ⊕ᴴ Lift Nil
                    )
                    (
                    TokenThrow
                    ⊕ Logger
                    ⊕ TokenizerResult
                    ⊕ Nil
                    )

eTokenizeElab = eBranch2
           ⊕ᴬ eLift
           ⊕ᴬ eLift
           ⊕ᴬ eLift
           ⊕ᴬ eNil


tokenizerᴴ : String -> ( List Token )
tokenizerᴴ str = fst  (un (givenHandle hResult
           (givenHandle hLogger
           (givenHandle hThrow (elaborate eTokenizeElab (tokenizeTextᴴ str) ) tt) tt) tt))
    where
        open import Control.Effect.Algebraic.Effect.Free using (_>>=_ ; _>>_)
        open import Control.Effect.Algebraic.Effect.RowInsert using (send ; Handler ; givenHandle)

tokenizerWithLogᴴ : String -> ( List Token × String × Maybe ⊤)
tokenizerWithLogᴴ str = (un (givenHandle hResult
           (givenHandle hLogger
           (givenHandle hThrow (elaborate eTokenizeElab (tokenizeTextᴴ str) ) tt) tt) tt))
    where
        open import Control.Effect.Algebraic.Effect.Free using (_>>=_ ; _>>_)
        open import Control.Effect.Algebraic.Effect.RowInsert using (send ; Handler ; givenHandle)

{-
testBig : tokenizerWithLogᴴ "wordd2 5" ≡ ( [] , "", nothing)
testBig = refl
-}
