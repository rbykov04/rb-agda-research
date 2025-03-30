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

record TokenStateRec : Set
    where
    constructor <_,_,_>
    field Input  : String
          Pos    : Nat
          Result : List Token
open TokenStateRec

TokenState = State TokenStateRec
TokenThrow = ThrowError (Nat × String)

throwError : {Effs : Effect} { A : Set  }
    → ⦃ TokenThrow ∈ Effs ⦄
    → Nat
    → String
    → Free Effs A
throwError pos text  = do
    x <- send (throwE (pos , text))
    ⊥-elim x

seeCharNum : {Effs : Effect}
    → ⦃ TokenState ∈ Effs ⦄
    → ⦃ TokenThrow ∈ Effs ⦄
    → Free Effs ( Char × Nat )
seeCharNum = do
    st <- send get
    case (head (Input st)) of λ where
        nothing → throwError (Pos st)  "unexpected end"
        (just ch) → pure (( ch , Pos st ))

seeChar : {Effs : Effect}
    → ⦃ TokenState ∈ Effs ⦄
    → ⦃ TokenThrow ∈ Effs ⦄
    → Free Effs Char
seeChar = do
    (ch , _) <- seeCharNum
    pure ch

isIdent1 : Char → Bool
isIdent1 c = primIsAlpha c ∨ primCharEquality c '_'

isIdent2 : Char → Bool
isIdent2 c = isIdent1 c ∨ primIsDigit c

popCharNum : {Effs : Effect}
    → ⦃ TokenState ∈ Effs ⦄
    → ⦃ TokenThrow ∈ Effs ⦄
    → Free Effs ( Char × Nat )
popCharNum = do
    < s , pos , res > <- send get
    case (uncons s) of λ where
        nothing → throwError pos  "unexpected end"
        (just (ch , xs)) → do
            send $ put < xs , pos + 1 , res >
            pure (( ch , pos))

popChar : {Effs : Effect}
    → ⦃ TokenState ∈ Effs ⦄
    → ⦃ TokenThrow ∈ Effs ⦄
    → Free Effs Char
popChar = do
    (ch , _) <- popCharNum
    pure ch

addToken : {Effs : Effect}
    → ⦃ TokenState ∈ Effs ⦄
    → ⦃ TokenThrow ∈ Effs ⦄
    → Token
    → Free Effs ⊤
addToken tok = do
    < s , pos , res >  <-  send get
    send $ put < s , pos , res ∷ʳ tok >

readWordM_ : {Effs : Effect}
    → ⦃ TokenState ∈ Effs ⦄
    → ⦃ TokenThrow ∈ Effs ⦄
    → Nat
    → String
    → Free Effs ⊤
readWordM_ begin str = do
    (c , num) <- seeCharNum
    if isIdent2 c
        then ( do
            ident <- popChar
            readWordM_ begin ( str ++ fromList (ident ∷ []) )
        ) else (addToken $ mkToken (Ident str) (num - begin) begin)
