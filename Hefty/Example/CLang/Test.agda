module Example.CLang.Test
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
open import Control.Effect.Algebraic.Effect.OpenUnion
open import Control.Effect.Algebraic.Effect.OpenUnion.Properties
open import Example.CLang.Tokenize


private
  variable
    a b c d e : Level
    A : Set a
    B : Set b
    C : Set c
    D : Set d
    E : Set e


test1 : tokenizer "word" ≡ mkToken (Ident "word") 0 4 ∷ []
test1 = refl

testword2 : tokenizer "word word2" ≡ mkToken (Ident "word") 0 4
                                    ∷ mkToken (Ident "word2") 0 10
                                    ∷ []
testword2 = refl


test2 : tokenizer "     " ≡ []
test2 = refl

test3 : tokenizer "1234" ≡ mkToken (Num 1234) 0 4 ∷ []
test3 = refl

test4 : tokenizer "0004" ≡ mkToken (Num 4) 0 4 ∷ []
test4 = refl


testBig : tokenizer "word 123 word2 5" ≡
                                    mkToken (Ident "word") 0 4
                                    ∷ mkToken (Num 123) 0 8
                                    ∷ mkToken (Ident "word2") 0 14
                                    ∷ mkToken (Num 5) 0 16
                                    ∷ []
testBig = refl


testBigLog2 : tokenizerWithLog "word 123 w w 3 w4" ≡ ( mkToken
                                                        (Ident
                                                         (wordTokenToStr
                                                          (suffix (suffix (suffix (token (mkAWord (symbol 'w'))) 'o') 'r')
                                                           'd')))
                                                        0 4
                                                        ∷
                                                        mkToken
                                                        (Num
                                                         (finishNum (addDigit (addDigit (token (mkANumber d1)) d2) d3)))
                                                        0 8
                                                        ∷
                                                        mkToken (Ident (wordTokenToStr (token (mkAWord (symbol 'w'))))) 0
                                                        10
                                                        ∷
                                                        mkToken (Ident (wordTokenToStr (token (mkAWord (symbol 'w'))))) 0
                                                        12
                                                        ∷
                                                        mkToken (Num (finishNum (token (mkANumber d3)))) 0 14 ∷
                                                        mkToken
                                                        (Ident
                                                         (wordTokenToStr (suffix (token (mkAWord (symbol 'w'))) '4')))
                                                        0 17
                                                        ∷ [] , "build is fail, let's add to list" ++
                                                                "\n" ++
                                                                ("mkAWord" ++ show 'w') ++
                                                                "\n" ++
                                                                ("continue build '" ++ show 'o' ++ "'") ++
                                                                "\n" ++
                                                                ("continue build '" ++ show 'r' ++ "'") ++
                                                                "\n" ++
                                                                ("continue build '" ++ show 'd' ++ "'") ++
                                                                "\n" ++
                                                                "build is fail, let's add to list" ++
                                                                "\n" ++
                                                                "build is fail, let's add to list" ++
                                                                "\n" ++
                                                                ("continue build '" ++ show '2' ++ "'") ++
                                                                "\n" ++
                                                                ("continue build '" ++ show '3' ++ "'") ++
                                                                "\n" ++
                                                                "build is fail, let's add to list" ++
                                                                "\n" ++
                                                                "build is fail, let's add to list" ++
                                                                "\n" ++
                                                                ("mkAWord" ++ show 'w') ++
                                                                "\n" ++
                                                                "build is fail, let's add to list" ++
                                                                "\n" ++
                                                                "build is fail, let's add to list" ++
                                                                "\n" ++
                                                                ("mkAWord" ++ show 'w') ++
                                                                "\n" ++
                                                                "build is fail, let's add to list" ++
                                                                "\n" ++
                                                                "build is fail, let's add to list" ++
                                                                "\n" ++
                                                                "build is fail, let's add to list" ++
                                                                "\n" ++
                                                                "build is fail, let's add to list" ++
                                                                "\n" ++
                                                                ("mkAWord" ++ show 'w') ++
                                                                "\n" ++
                                                                ("continue build '" ++ show '4' ++ "'") ++
                                                                "\n" ++ "add last token" ++ "\n" ++ "" , (just tt))
testBigLog2 = refl
