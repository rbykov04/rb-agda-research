module Main where
import System.IO

-- the first attempt
data Expr' = Val' Int | Add' Expr' Expr'

eval :: Expr' -> Int
eval (Val' x)   = x
eval (Add' x y) = eval x + eval y

render :: Expr' -> String
render (Val' x) = show x
render (Add' x y) = "(" ++ render x ++ " + " ++ render y ++ ")"

example1 :: Expr'
example1 = Add' (Val' 10) (Add' (Val' 10) (Val' 10))


-- the second attempt
-- It is crazy
data Expr f  = In (f (Expr f))

data Val e   = Val Int
type IntExpr = Expr Val

data Add e   = Add e e
type AddExpr = Expr Add

data (f :+: g) e = Inl (f e) | Inr (g e)  -- It is a sum or coProduct

example2 :: Expr (Val :+: Add)
example2 = In (Inr (Add (In (Inl (Val 118)))(In (Inl (Val 1219)))))


main :: IO ()
main = do
  putStrLn $ render example1
