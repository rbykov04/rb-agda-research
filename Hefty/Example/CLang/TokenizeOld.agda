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
open import Control.Effect.Algebraic.HighOrder.Lift.OpenUnion
open import Control.Effect.Algebraic.Hefty.RowInsert

private
  variable
    a b c d e : Level
    A : Set a
    B : Set b
    C : Set c
    D : Set d
    E : Set e

data TokenKind : Set
    where
    EOF     : TokenKind
    Ident   : String -> TokenKind
    Punct   : String -> TokenKind
    Num     : Nat    -> TokenKind
    Keyword : String -> TokenKind

record Token : Set
    where
    constructor mkToken
    field tokenKind : TokenKind
          tokenLen  : Nat
          tokenLoc  : Nat
open Token public

data TokenizerOp : Set1
    where
    addToken : Token → TokenizerOp

TokenizerResult : FirstEffect
TokenizerResult = record
    { Op = TokenizerOp
    ; Ret = λ where
        (addToken _)  → ⊤
    }

data LoggerOp : Set1
    where
    log : String → LoggerOp


Logger : FirstEffect
Logger = record
    { Op = LoggerOp
    ; Ret = λ where
        (log _)  → ⊤
    }


TokenThrow = ThrowError (Nat × String)


show : Char -> String
show ch = fromList (ch ∷ [])

throwError : {Effs E : Effect} { A : Set  }
    → ⦃ effrow Effs ＝ TokenThrow ∣ E ⦄
    → Nat
    → String
    → Free Effs A
throwError pos text  = do
        x <- send (throwE (pos , text))
        ⊥-elim x
    where open import Control.Effect.Algebraic.Effect.Free using (_>>=_ ; _>>_)

throwErrorᴴ : {H H' : Effectᴴ} { A : Set  }
    → ⦃ heftyrow H ＝ (Lift TokenThrow) ∣ H' ⦄
    → Nat
    → String
    → Hefty H A
throwErrorᴴ pos text  = do
        x <- up (throwE (pos , text))
        ⊥-elim x
    where open import Control.Effect.Algebraic.Hefty using (_>>=_ ; _>>_)



isIdent1 : Char → Bool
isIdent1 c = primIsAlpha c ∨ primCharEquality c '_'

isIdent2 : Char → Bool
isIdent2 c = isIdent1 c ∨ primIsDigit c

isSeparator : Char → Bool
isSeparator c = primIsSpace c

unconsList : {A : Set} -> List A -> Maybe ( A × List A )
unconsList [] = nothing
unconsList (x ∷ st) = just (x , st )


Stream = (List Char × Nat)

data WordToken : Set
  where
    symbol : Char -> WordToken
    suffix : WordToken -> Char -> WordToken

word_ : WordToken
word_ = suffix (suffix (suffix (suffix (symbol 'h') 'e') 'l') 'l') 'o'

buildWord : WordToken → Char → Maybe WordToken
buildWord x ch = if isIdent2 ch then just $ suffix x ch else nothing

wordTokenToStr : WordToken → String
wordTokenToStr (symbol ch) = show ch
wordTokenToStr (suffix suf ch) = wordTokenToStr suf ++ show ch




charToWord : Char → Maybe WordToken
charToWord ch = if isIdent2 ch then just $ symbol ch else nothing


data Digit : Set
    where
        d0 : Digit
        d1 : Digit
        d2 : Digit
        d3 : Digit
        d4 : Digit
        d5 : Digit
        d6 : Digit
        d7 : Digit
        d8 : Digit
        d9 : Digit

charToDigit : Char → Maybe Digit
charToDigit '0' = just d0
charToDigit '1' = just d1
charToDigit '2' = just d2
charToDigit '3' = just d3
charToDigit '4' = just d4
charToDigit '5' = just d5
charToDigit '6' = just d6
charToDigit '7' = just d7
charToDigit '8' = just d8
charToDigit '9' = just d9
charToDigit ch = nothing

digitToNat : Digit → Nat
digitToNat d0 = 0
digitToNat d1 = 1
digitToNat d2 = 2
digitToNat d3 = 3
digitToNat d4 = 4
digitToNat d5 = 5
digitToNat d6 = 6
digitToNat d7 = 7
digitToNat d8 = 8
digitToNat d9 = 9

data NumToken : Set
    where
      digit : Digit -> NumToken     -- pure
      addDigit : NumToken → Digit → NumToken -- impure

buildNum : NumToken → Char → Maybe NumToken
buildNum x ch = case charToDigit ch of λ where
                    (just d) -> just $ addDigit x d
                    nothing -> nothing

finishNum : NumToken → Nat
finishNum (digit d) = digitToNat d
finishNum (addDigit num d) = digitToNat d + (10 * finishNum num) -- Maybe there is an error, but who care, it is an example

data Space : Set
    where
    space : Space


buildSpace : Space → Char → Maybe Space
buildSpace sp ch = if isSeparator ch
                   ∨ primCharEquality ch '\n'
                   ∨ primCharEquality ch '\0'
                      then just sp
                      else nothing

record AToken : Set1
    where
    field tokenT : Set
          token  : tokenT
          build  : tokenT → Char → Maybe tokenT
          finish : tokenT → Maybe TokenKind
open AToken public

mkAWord : WordToken → AToken
mkAWord ch = record
    { tokenT = WordToken
    ; token = ch
    ; build = buildWord
    ; finish = λ x → just  (Ident (wordTokenToStr x))
    }


mkANumber : Digit → AToken
mkANumber d = record
    { tokenT = NumToken
    ; token = digit d
    ; build = buildNum
    ; finish = λ x → just (Num (finishNum x))
    }

mkASpace : Space → AToken
mkASpace _ = record
    { tokenT = Space
    ; token = space
    ; build = buildSpace
    ; finish = λ z → nothing
    }


record Parser : Set2
    where
    constructor mkParser
    field pos  : Nat
          atok : AToken
open Parser

nextstep : Parser → AToken → Parser
nextstep parser newAtok = mkParser (suc $ pos parser) newAtok


tokenize : {Effs E1 E2 E3 : Effect}
    → ⦃ effrow Effs ＝ TokenizerResult ∣ E1 ⦄
    → ⦃ effrow Effs ＝ Logger ∣ E2 ⦄
    → ⦃ effrow Effs ＝ TokenThrow ∣ E3 ⦄
    → List Char
    → Parser
    → Free Effs ⊤
tokenize [] parser = do
    case finish (atok parser) (token (atok parser)) of λ where
        nothing          → pure tt
        (just tokenKind) → do
          send $ log ("add last token")
          send $ addToken (mkToken tokenKind 0 (pos parser))
    where
        open import Control.Effect.Algebraic.Effect.Free using (_>>=_ ; _>>_)
tokenize (ch ∷ text) parser =
    case build (atok parser) (token (atok parser)) ch of λ where
        nothing  → do
            send $ log ("build is fail, let's add to list")
            case finish (atok parser) (token (atok parser)) of λ where
                (just tokenKind) → do
                    send $ addToken (mkToken tokenKind 0 (pos parser))
                    case charToDigit ch of λ where
                        (just d) → tokenize text (nextstep parser (mkANumber d))
                        nothing  → case charToWord ch of λ where
                            (just symb) → do
                                send $ log ("mkAWord" ++ show ch)
                                tokenize text (nextstep parser (mkAWord symb))
                            nothing  → case buildSpace space ch of λ where
                                (just sp) → tokenize text (nextstep parser (mkASpace sp))
                                nothing → throwError (pos parser) ("invalid token: " ++ show ch)
                nothing          → do
                    case charToDigit ch of λ where
                        (just d) → tokenize text (nextstep parser (mkANumber d))
                        nothing  → case charToWord ch of λ where
                            (just symb) → do
                                send $ log ("mkAWord" ++ show ch)
                                tokenize text (nextstep parser (mkAWord symb))
                            nothing  → case buildSpace space ch of λ where
                                (just sp) → tokenize text (nextstep parser (mkASpace sp))
                                nothing → throwError (pos parser) ("invalid token: " ++ show ch)
        (just newATok) → do
            send $ log ("continue build '" ++ show ch ++ "'")
            tokenize text (record
                {pos = suc $ pos parser
                ; atok = record
                { tokenT = tokenT $ atok parser
                ; token  = newATok
                ; build  = build $ atok parser
                ; finish = finish $ atok parser } })
    where
        open import Control.Effect.Algebraic.Effect.Free using (_>>=_ ; _>>_)

tokenizeText : {Effs E1 E2 E3 : Effect}
    → ⦃ effrow Effs ＝ TokenizerResult ∣ E1 ⦄
    → ⦃ effrow Effs ＝ Logger ∣ E2 ⦄
    → ⦃ effrow Effs ＝ TokenThrow ∣ E3 ⦄
    → String
    → Free Effs ⊤
tokenizeText text = tokenize (toList text ) (mkParser 0 (mkASpace space))


hResult : {Effs : Effect} -> Handler A TokenizerResult ⊤ (List Token × A ) Effs
hResult .ret x _ = pure ([] , x)
hResult .hdl (addToken tok) k p = do
    (s' , x) <- k tt p
    pure ((tok ∷ s') , x)
    where
        open import Control.Effect.Algebraic.Effect.Free using (_>>=_ ; _>>_)
        open import Control.Effect.Algebraic.Effect.OpenUnion.Properties using (send ; Handler ; givenHandle)

hLogger : {Effs : Effect} -> Handler A Logger ⊤ (String × A ) Effs
hLogger .ret x _ = pure ("" ,  x)
hLogger .hdl (log str) k p = do
    (s' , x) <- k tt p
    pure ((str ++ "\n" ++ s') , x)
    where
        open import Control.Effect.Algebraic.Effect.Free using (_>>=_ ; _>>_)
        open import Control.Effect.Algebraic.Effect.OpenUnion.Properties using (send ; Handler ; givenHandle)


hThrow : {Effs : Effect} -> Handler A TokenThrow ⊤ (Maybe A) Effs
hThrow .ret x _ = pure (just x)
hThrow .hdl (throwE code) k x = pure nothing


tokenizer : String -> ( List Token )
tokenizer str = fst  (un (givenHandle hResult
           (givenHandle hLogger
           (givenHandle hThrow (tokenizeText str) tt) tt) tt))
    where
        open import Control.Effect.Algebraic.Effect.Free using (_>>=_ ; _>>_)


tokenizerWithLog : String -> ( List Token × String × Maybe ⊤ )
tokenizerWithLog str = un (givenHandle hResult
           (givenHandle hLogger
           (givenHandle hThrow (tokenizeText str) tt) tt) tt)
    where
        open import Control.Effect.Algebraic.Effect.Free using (_>>=_ ; _>>_)

data BranchOp : Set1 where
    branch : BranchOp

Branch : HighEffect
Branch .Opᴴ = BranchOp
Branch .Fork x = Nil
Branch .Retᴴ branch = Bool

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

tokenizerWithLog1 : String -> ( List Token × String × Maybe ⊤ )
tokenizerWithLog1 str = un (givenHandle hResult
           (givenHandle hLogger
           (givenHandle hThrow (tokenizeText str) tt) tt) tt)


{-

eBranch : {Effs E1 E2 E3 : Effect}
    → ⦃ effrow Effs ＝ TokenizerResult ∣ E1 ⦄
    → ⦃ effrow Effs ＝ Logger ∣ E2 ⦄
    → ⦃ effrow Effs ＝ TokenThrow ∣ E3 ⦄
    → Elaboration Branch Effs
eBranch .alg branch fork k = do
    o <- k true
    {-
    x <- (# givenHandle hResult
        (givenHandle hLogger
        (givenHandle hThrow {!k ?!} {!!}) {!!}) {!!})
    -}
    {!!}
    k true
    k false
    where
        open import Control.Effect.Algebraic.Effect.Free using (_>>=_ ; _>>_)
        open import Control.Effect.Algebraic.Effect.RowInsert using (send ; Handler ; givenHandle)

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

eTokenizeElab = eBranch
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

-}
