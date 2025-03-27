{-# OPTIONS  --backtracking-instance-search  #-}
module Example.Teletype where

open import Agda.Builtin.Unit
open import Agda.Builtin.Sigma
open import Agda.Builtin.List
open import Agda.Builtin.Char
open import Agda.Builtin.String
open import Agda.Builtin.IO
open import Agda.Primitive

open import Mystdlib.Mystdlib

open import Effect.Core.Free
open import Effect.Free.Output
open import Effect.Free.Throw
open import Effect.Free.Nil
open import Effect.Free.Teletype
open import Effect.Free.State Char

private
  variable
    a b c d e : Level
    A : Set a
    B : Set b
    C : Set c
    D : Set d
    E : Set e

program1 : Free Teletype ⊤
program1 =
          impure (putChar 'H')              \ _ ->
          impure (putChar 'E')              \ _ ->
          impure (putChar 'L')              \ _ ->
          impure (putChar 'L')              \ _ ->
          impure (putChar 'L')              \ _ ->
          impure (putChar 'O')              \ _ ->
          impure (putChar '\n')             \ _ ->
          impure getChar                    \ a ->
          impure getChar                    \ b ->
          impure getChar                    \ c ->
          impure getChar                    \ d ->
          impure (putChar 'a')              \ _ ->
          impure (putChar '=')              \ _ ->
          impure (putChar a)                \ _ ->
          impure (putChar '\n')             \ _ ->
          impure (putChar 'b')              \ _ ->
          impure (putChar '=')              \ _ ->
          impure (putChar b)                \ _ ->
          impure (putChar '\n')             \ _ ->
          impure (putChar 'c')              \ _ ->
          impure (putChar '=')              \ _ ->
          impure (putChar c)                \ _ ->
          impure (putChar '\n')             \ _ ->
          impure (putChar 'd')              \ _ ->
          impure (putChar '=')              \ _ ->
          impure (putChar d)                \ _ ->
          impure (putChar '\n')             \ _ ->
          impure (putChar 'E')              \ _ ->
          impure (putChar 'N')              \ _ ->
          impure (putChar 'D')              \ _ ->
          impure (putChar '\n')             \ _ ->
          pure tt


program5 : {E Here : Effect}
      -> {{ EffectStorage (Output |> State |> Teletype) Here Teletype }}
      -> Free ( Output |> State |> Teletype) ⊤
program5 = do
    ch <- `get
    `putChar ch
    `put ch


program6 : Free ( State |> Teletype) ⊤
program6 = do
    ch <- `get
    `putChar ch



program2 : Free ( State |> Teletype) ⊤
program2 = do
    putStrLn "\nCheck State"
    putStrLn "\n"
    putStrLn "Put3"
    `put 'z'

program3 : Free ( Output |> State |> Nil) ⊤
program3 = do
    `put 'z'

program4 : Free ( Output |> State |> Teletype) ⊤
program4 = do
    `put 'z'

main1 : IO ⊤
main1 = exec program1


program : Free (coProduct State Teletype) ⊤
program = do
    putStrLn "Check def"
    def <- `get
    `putChar def
    `put 'a'
    a <- `get
    putStrLn "\nCheck State"
    `putChar a
    putStrLn "\n"
    h1 <- `getChar
    `putChar h1
    `putChar h1
    `putChar h1
    putStrLn "Put2"
    h2 <- `getChar
    `putChar h2
    putStrLn "Put3"

main : IO ⊤
main = exec (givenHandle hSt program 'z') >>>= \ x -> return tt
