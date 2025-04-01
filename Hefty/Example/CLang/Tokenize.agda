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

open import Foundation.Base
open import Data.String.Base
open import Data.Vec.Base

open import Control.Effect.Algebraic.FirstOrder.State
open import Control.Effect.Algebraic.FirstOrder.Throw
open import Control.Effect.Algebraic.Effect
open import Control.Effect.Algebraic.Effect.Free
open import Control.Effect.Algebraic.Effect.OpenUnion
open import Control.Effect.Algebraic.Effect.OpenUnion.Properties

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
open Token

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

throwError : {Effs : Effect} { A : Set  }
    → ⦃ TokenThrow ∈ Effs ⦄
    → Nat
    → String
    → Free Effs A
throwError pos text  = do
    x <- send (throwE (pos , text))
    ⊥-elim x

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

data NumToken : Set
    where
      digit : Digit -> NumToken     -- pure
      addDigit : NumToken → Digit → NumToken -- impure

buildNum : NumToken → Char → Maybe NumToken
buildNum x ch = case charToDigit ch of λ where
                    (just d) -> just $ addDigit x d
                    nothing -> nothing


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
open AToken

mkAWord : WordToken → AToken
mkAWord ch = record
    { tokenT = WordToken
    ; token = ch
    ; build = buildWord
    ; finish = λ x → nothing -- Fixme
    }


mkANumber : Digit → AToken
mkANumber d = record
    { tokenT = NumToken
    ; token = digit d
    ; build = buildNum
    ; finish = λ z → nothing -- FIXME
    }

mkASpace : Space → AToken
mkASpace _ = record
    { tokenT = Space
    ; token = space
    ; build = buildSpace
    ; finish = λ z → nothing -- FIXME
    }


record Parser : Set2
    where
    constructor mkParser
    field pos  : Nat
          atok : AToken
open Parser

nextstep : Parser → AToken → Parser
nextstep parser newAtok = mkParser (suc $ pos parser) newAtok


tokenize : {Effs : Effect}
    → ⦃ TokenizerResult ∈ Effs ⦄
    → ⦃ Logger ∈ Effs ⦄
    → ⦃ TokenThrow ∈ Effs ⦄
    → List Char
    → Parser
    → Free Effs ⊤
tokenize [] parser =
    case finish (atok parser) (token (atok parser)) of λ where
        nothing          → pure tt
        (just tokenKind) → do
          send $ addToken (mkToken tokenKind 0 (pos parser))
tokenize (ch ∷ text) parser =
    case build (atok parser) (token (atok parser)) ch of λ where
        nothing  → case charToDigit ch of λ where
            (just d) → tokenize text (nextstep parser (mkANumber d))
            nothing  → case charToWord ch of λ where
                (just symb) → tokenize text (nextstep parser (mkAWord symb))
                nothing  → case buildSpace space ch of λ where
                    (just sp) → tokenize text (nextstep parser (mkASpace sp))
                    nothing → throwError (pos parser) ("invalid token: " ++ show ch)
        (just newATok) → tokenize text (record
            {pos = suc $ pos parser
            ; atok = record
              { tokenT = tokenT $ atok parser
              ; token  = newATok
              ; build  = build $ atok parser
              ; finish = finish $ atok parser } })
