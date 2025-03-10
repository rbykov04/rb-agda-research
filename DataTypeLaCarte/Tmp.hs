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

add :: Expr Add -> Expr Add -> Expr Add
add x y = In (Add x y)


example-my1 =
  let
    a       = In (Inl (Val 118))
    b       = In (Inl (Val 1219))
    add-res = Add a b
    res     = Inr (add-res)
  in In res


valId :: Int -> Expr Val
valId x = In (Val x)

value1 :: Int -> Val e
value1 x = Val x

value2 :: Int -> (Val :+: f ) e
value2 x = Inl (Val x)

value3 :: Int -> (Val :+: f :+: g ) e
value3 x = Inl (Inl (Val x))

value4 :: Int -> (Val :+: f :+: g :+: d ) e
value4 x = Inl (Inl (Inl (Val x)))

valL :: Int -> Expr (Val :+: f)
valL x = In (value2 x)

valL2 :: Int -> Expr (Val :+: f :+: g)
valL2 x = In (value3 x)

valL3 :: Int -> Expr (Val :+: f :+: g :+: d)
valL3 x = In (value4 x)


valL' :: Int -> Expr (Val :+: f)
valL' x = In (Inl (Val x))

valL2' :: Int -> Expr (Val :+: f :+: g)
valL2' x = In (Inl (Inl (Val x)))


valL3' :: Int -> Expr (Val :+: f :+: g :+: d)
valL3' x = In (Inl (Inl (Inl (Val x))))



valR :: Int -> Expr (f :+: Val)
valR x = In (Inr (Val x))

valR2 :: Int -> Expr (f :+: g :+: Val)
valR2 x = In (Inr (Val x))

valR3 :: Int -> Expr (e :+: f :+: f :+: Val)
valR3 x = In (Inr (Val x))


value1'' :: Int -> Val e
value1'' x = Val x

value2'' :: Int -> (Val :+: f ) e
value2'' x = Inl (value1'' x)

value3'' :: Int -> (Val :+: f :+: g ) e
value3'' x = Inl (value2'' x)

value4'' :: Int -> (Val :+: f :+: g :+: d ) e
value4'' x = Inl (value3'' x)

valL'' :: Int -> Expr (Val :+: f)
valL'' x = In (value2'' x)

valL2'' :: Int -> Expr (Val :+: f :+: g)
valL2'' x = In (value3'' x)

valL3'' :: Int -> Expr (Val :+: f :+: g :+: d)
valL3'' x = In (value4'' x)

--Let's use class

-- Next step
class SmartValue sum where
  mkValue :: Int -> (sum) e

--id
instance SmartValue (Val) where
  mkValue x = Val x

instance SmartValue (Val :+: f) where
  mkValue x = Inl (Val x)

instance SmartValue (Val :+: f :+: g) where
  mkValue x = Inl (Inl (Val x))

instance SmartValue (Val :+: f :+: g :+: d) where
  mkValue x = Inl (Inl (Inl (Val x)))


value3''' :: Int -> (Val :+: f :+: g ) e
value3''' x = Inl (mkValue x)

value4''' :: Int -> (Val :+: f :+: g :+: d ) e
value4''' x = Inl (mkValue x)

valL''' :: Int -> Expr (Val :+: f)
valL''' x = In (mkValue x)

valL2''' :: Int -> Expr (Val :+: f :+: g)
valL2''' x = In (mkValue x)

valL3''' :: Int -> Expr (Val :+: f :+: g :+: d)
valL3''' x = In (mkValue x)

-- Next step
class SmartValue1 sum where
  mkValue1 :: Int -> (sum) e

--id
instance SmartValue1 (Val) where
  mkValue1 x = Val x

instance SmartValue1 (Val :+: f) where
  mkValue1 x = Inl (mkValue1 x)

instance SmartValue1 (Val :+: f :+: g) where
  mkValue1 x = Inl (mkValue1 x)

instance SmartValue1 (Val :+: f :+: g :+: d) where
  mkValue1 x = Inl (mkValue1 x)


value3v4 :: Int -> (Val :+: f :+: g ) e
value3v4 x = Inl (mkValue1 x)

value4v4 :: Int -> (Val :+: f :+: g :+: d ) e
value4v4 x = Inl (mkValue1 x)

valLv4 :: Int -> Expr (Val :+: f)
valLv4 x = In (mkValue1 x)

valL2v4 :: Int -> Expr (Val :+: f :+: g)
valL2v4 x = In (mkValue1 x)

valL3v4 :: Int -> Expr (Val :+: f :+: g :+: d)
valL3v4 x = In (mkValue1 x)

-- Next step

class Inject sub sup where
  injj :: sub a -> sup a

instance Inject a a where
  injj = id


instance Inject a (a :+: b) where
  injj = Inl


instance (Inject f g) => (Inject f (h :+: g)) where
  injj = Inr . injj


--instance (Functor f, Functor g, Functor h, f :<: g) => f :<: (h :+: g) where

value31v5 :: Int -> Val e
value31v5 x = injj (Val x)

value2v5 :: Int -> (Val :+: f) e
value2v5 x = injj (Val x)

value3v5 :: (Inject Val g) => Int -> (Val :+: f :+: g ) e
value3v5 x = injj ( Val x)

value4v5 :: (Inject Val d) => Int -> (Val :+: f :+: g :+: d) e
value4v5 x = injj ( Val x)


-- Think about this:
inject1 :: (Inject g  f) => g (Expr f) -> Expr f
inject1 = In . injj

mkValueV :: (Inject Val f) => Int -> Expr f
mkValueV x = inject1 (Val x)

--Step back
class Inject1 sub sup where
  inj1 :: sub  -> sup

instance Inject1 a a where
  inj1 = id

instance Inject1 (a e) ((a :+: b) e) where
  inj1 = Inl


instance (Inject1 (f e) (g e)) => (Inject1 (f e) ((h :+: g) e)) where
  inj1 = Inr . inj1


--instance (Functor f, Functor g, Functor h, f :<: g) => f :<: (h :+: g) where
{-
value31v5 :: Int -> Val e
value31v5 x = injj (Val x)

value2v5 :: Int -> (Val :+: f) e
value2v5 x = injj (Val x)

value3v5 :: (Inject Val g) => Int -> (Val :+: f :+: g ) e
value3v5 x = injj ( Val x)

value4v5 :: (Inject Val d) => Int -> (Val :+: f :+: g :+: d) e
value4v5 x = injj ( Val x)
-}



add2 :: Expr (Val :+: Add) -> Expr (Val :+: Add) -> Expr (Val :+: Add)
add2 x y =
  let
    add-res = Add x y
    res     = Inr (add-res)
  in In res

addr :: Expr (f :+: Add) -> Expr (f :+: Add) -> Expr (f :+: Add)
addr x y =
  let
    add-res = Add x y
    res     = Inr (add-res)
  in In res

addl :: Expr (Add :+: f)  -> Expr (Add :+: f) -> Expr (Add :+: f)
addl x y =
  let
    add-res = Add x y
    res     = Inl (add-res)
  in In res

examplemy :: Expr (Val :+: Add)
examplemy = addr (valL 1) (valL 3)


examplemy2 :: Expr (Add :+: Val)
examplemy2 = addl (valR 1) (valR 3)

examplemy3 :: Expr (Val)
examplemy3 = val' 3

examplemy4 :: Expr (Val :+: Val)
examplemy4 = valL 3

examplemy5 :: Expr (Val :+: Val)
examplemy5 = valR 3


examplemy6 :: Expr (Val :+: Val :+: Val)
examplemy6 = valR 3

examplemy51 :: Expr (Val :+: Val :+: Val)
examplemy51 = valL2 3

examplemy52 :: Expr (Val :+: Val :+: Val)
examplemy52 = valL2' 3


{-
Problem with
-}
data Sub e   = Sub e e
examplemy7 :: Expr (Add :+: Sub :+: Val)
examplemy7 = valR 3




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
