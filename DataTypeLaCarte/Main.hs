{-# LANGUAGE OverlappingInstances #-}
module Main where
import System.IO

-- the first attempt
data Expr' = Val' Int | Add' Expr' Expr'

eval' :: Expr' -> Int
eval' (Val' x)   = x
eval' (Add' x y) = eval' x + eval' y

render :: Expr' -> String
render (Val' x) = show x
render (Add' x y) = "(" ++ render x ++ " + " ++ render y ++ ")"

example1 :: Expr'
example1 = Add' (Val' 10) (Add' (Val' 10) (Val' 10))


-- Part 2
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

-- Part 3
instance Functor Val where
  fmap f (Val x) = Val x

instance Functor Add where
  fmap f (Add e1 e2) = Add (f e1) (f e2)

instance (Functor f, Functor g) => Functor (f :+: g) where
  fmap f (Inl e1) = Inl (fmap f e1)
  fmap f (Inr e2) = Inr (fmap f e2)

--                       algebra
--                         |
foldExpr :: Functor f => (f a -> a) -> Expr f -> a
foldExpr f (In t) = f (fmap (foldExpr f) t)
-- Algebra specifies one step of recurison
-- It is look tree pass

class Functor f => Eval f where
  evalAlgebra :: f Int -> Int
--  Int as result is out choise

instance Eval Val where
  evalAlgebra (Val x) = x

instance Eval Add where
  evalAlgebra (Add x y) = x + y

instance (Eval f, Eval g) => Eval (f :+: g) where
  evalAlgebra (Inl x) = evalAlgebra x
  evalAlgebra (Inr y) = evalAlgebra y

eval :: Eval f => Expr f -> Int
eval expr = foldExpr evalAlgebra expr

-- Part4
-- the first attempt
val' :: Int -> Expr Val
val' x = In (Val x)


infixl 6 !+!
(!+!) :: Expr Add -> Expr Add -> Expr Add
x !+! y = In (Add x y)
{-
example3 = val' 1 !+! val' 3

Main.hs:80:21: error:
    • Couldn't match type ‘Val’ with ‘Add’
      Expected: Expr Add
        Actual: Expr Val
    • In the second argument of ‘(+!)’, namely ‘val' 3’
      In the expression: val' 1 +! val' 3
      In an equation for ‘example3’: example3 = val' 1 +! val' 3
   |
80 | example3 = val' 1 +! val' 3
   |                     ^^^^^
-}

-- smart constructors:
class (Functor sub, Functor sup) => sub :<: sup where
  inj :: sub a -> sup a
-- |
-- injection

-- This is crazy:

-- Reflexifity
instance Functor f => f :<: f where
  inj = id

-- "The second instance explains how to
-- inject any value of type f a to a value of type (f :+: g) a"
instance (Functor f, Functor g) => f :<: (f :+: g) where
  inj = Inl

--The third
--instance asserts that provided we can inject a value of type f a into one of type g a,
--we can also inject f a into a larger type (h :+: g) a by composing the first injection
--with an additional Inr.
instance (Functor f, Functor g, Functor h, f :<: g) => f :<: (h :+: g) where
  inj = Inr . inj


infixl 6 |+|

-- Think about this:
inject :: g :<: f => g (Expr f) -> Expr f
inject = In . inj

val   :: (Val :<: f) => Int -> Expr f
val x = inject (Val x)

(|+|) :: (Add :<: f) => Expr f -> Expr f -> Expr f
x |+| y = inject (Add x y)
-- Add :<: f - any signature f that supports addition

example3 :: Expr (Add :+: Val)
example3 = (val 3000 |+| val 1330) |+| val 7


-- From this moment we need {# LANGUAGE OverlappingInstances #-}
-- Without this: For example
inVal :: Int -> Expr (Val :+: Val)
inVal i = inject (Val i)
--Which injection should be inferred, Inl or Inr? T
--(In (Inl (Val x))) and eval (In (Inr (Val x)))?

-- Let's run
main :: IO ()
main = do
  putStrLn "Part1"
  putStrLn $ (render example1) ++ " => " ++ show (eval' example1)
  putStrLn "Part3"
  putStrLn $ " => " ++ show (eval example2)
