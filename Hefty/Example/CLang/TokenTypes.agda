module Example.CLang.TokenTypes
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


show : Char -> String
show ch = fromList (ch ∷ [])


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
open Parser public

nextstep : Parser → AToken → Parser
nextstep parser newAtok = mkParser (suc $ pos parser) newAtok

