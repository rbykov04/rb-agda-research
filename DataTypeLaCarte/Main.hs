module Main where
import System.IO

-- the first attempt
data Expr' = Val' Int | Add' Expr' Expr'

eval' :: Expr' -> Int
eval' (Val' x)   = x
eval' (Add' x y) = eval' x + eval' y

render' :: Expr' -> String
render' (Val' x) = show x
render' (Add' x y) = "(" ++ render' x ++ " + " ++ render' y ++ ")"

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


infixr 6 :+:
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
  prj :: sup a -> Maybe (sub a)

-- This is crazy:

-- Reflexifity
instance {-# OVERLAPPABLE #-} Functor f => f :<: f where
  inj = id
  prj = Just . id

-- "The second instance explains how to
-- inject any value of type f a to a value of type (f :+: g) a"
instance {-# OVERLAPPABLE #-} (Functor f, Functor g) => f :<: (f :+: g) where
  inj = Inl

  prj (Inl x) = Just x
  prj (Inr x) = Nothing

--The third
--instance asserts that provided we can inject a value of type f a into one of type g a,
--we can also inject f a into a larger type (h :+: g) a by composing the first injection
--with an additional Inr.
instance {-# OVERLAPPABLE #-} (Functor f, Functor g, Functor h, f :<: g) => f :<: (h :+: g) where
  inj = Inr . inj

  prj (Inl x) = Nothing
  prj (Inr x) = prj x


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
example3 = val 3000 |+| val 1330 |+| val 7


-- From this moment we need {# LANGUAGE OverlappingInstances #-}
-- Without this: For example
inVal :: Int -> Expr (Val :+: Val)
inVal i = inject (Val i)
--Which injection should be inferred, Inl or Inr? T
--(In (Inl (Val x))) and eval (In (Inr (Val x)))?

-- part 5

data Mul x = Mul x x

instance Functor Mul where
  fmap f (Mul x y) = Mul (f x) (f y)


instance Eval Mul where
  evalAlgebra (Mul x y) = x * y

infixl 7 |*|

(|*|) :: (Mul :<: f) => Expr f -> Expr f -> Expr f
x |*| y = inject (Mul x y)

--example4 :: Expr (Val :+: Add :+: Mul)
example4 :: Expr (Val :+: Add :+: Mul)
example4 = val 80 |*| val 5 |+| val 4

example5 :: Expr (Val :+: Add :+: Mul)
example5 = val 6 |*| val 7

class Render f where
  render :: Render g => f (Expr g)  -> String

pretty :: Render f => Expr f -> String
pretty (In e) = render e

instance Render Val where
  render (Val x) = show x

instance (Render f, Render g) => Render (f :+: g) where
  render (Inl x) = render x
  render (Inr x) = render x

instance Render Add where
  render (Add x y) = "(" ++ pretty x ++ " + " ++ pretty y ++ ")"

instance Render Mul where
  render (Mul x y) = "(" ++ pretty x ++ " * " ++ pretty y ++ ")"


match :: (g :<: f) => Expr f -> Maybe (g (Expr f))
match (In e) = prj e

distr :: (Add :<:f , Mul :<: f) => Expr f -> Maybe (Expr f)
distr t = do
  Mul a b <- match t
  Add c d <- match b
  return (a |*| c |+| a |*| d)


tryDistr :: (Add :<:f , Mul :<: f) => Expr f -> Expr f
tryDistr e = case distr e of
  (Just x) -> x
  Nothing  -> e


example6 :: Expr (Val :+: Add :+: Mul)
example6 = val 80 |*| (val 5 |+| val 4)


-- Part 6 Monands for Free

data Term f a =
    Pure a
  | Impure (f (Term f a))

instance Functor f => Functor (Term f) where
  fmap f (Pure x)   = Pure (f x)
  fmap f (Impure t) = Impure (fmap (fmap f) t) -- ????

-- this is written with GigaChat
-- there is not anything about this in Paper
-- and then fix with this: https://www.extrema.is/blog/2022/04/04/data-types-a-la-carte
instance Functor f => Applicative (Term f) where
  pure                 = Pure
  Pure f <*> Pure x    = Pure (f x)
  Pure f <*> Impure tx = Impure (fmap (f <$>) tx)
  Impure tf <*> ta = Impure (fmap (\func -> func <*> ta) tf)


instance Functor f => Monad (Term f) where
  return x         = Pure x

  (Pure x) >>= f   = f x
  (Impure t) >>= f = Impure (fmap (>>=f) t)

-- They are also Free Monads:
data Zero a            -- Identity monad
data One a     = One   -- Maybe monad
data Const e a = Const -- Error monad

-- Add memory to our calc
data Incr t = Incr Int t          deriving (Functor)
data Recall t = Recall (Int -> t) deriving (Functor)

injectM :: (g :<: f) => g (Term f a) -> Term f a
injectM = Impure . inj

incr :: (Incr :<: f) => Int -> Term f ()
incr i = injectM (Incr i (Pure ()))

recall :: (Recall :<: f) => Term f Int
recall = injectM (Recall Pure)

tick :: Term (Recall :+: Incr) Int
tick = do y <- recall
          incr 1
          return y

--- ???
foldTerm :: Functor f => (a -> b) -> (f b -> b) -> Term f a -> b
foldTerm pure imp (Pure x)   = pure x
foldTerm pure imp (Impure t) = imp (fmap (foldTerm pure imp) t)

newtype Mem = Mem Int deriving Show

class Functor f => Run f where
  runAlgebra :: f (Mem -> (a, Mem)) -> Mem -> (a, Mem)

instance Run Incr where
  runAlgebra (Incr x save) (Mem i) = save (Mem (i + x))

instance Run Recall where
  runAlgebra (Recall f) (Mem i) = f i (Mem i)

instance (Run f, Run g) => Run (f :+: g) where
  runAlgebra (Inl x) = runAlgebra x
  runAlgebra (Inr y) = runAlgebra y


run :: Run f => Term f a -> Mem -> (a, Mem)
run = foldTerm (,) runAlgebra

data Teletype a =
    GetChar (Char -> a)
  | PutChar Char a
  deriving Functor

data Filesystem a =
    ReadFile  FilePath (String -> a)
  | WriteFile FilePath String a
  deriving Functor

class Functor f => Exec f where
  execAlgebra :: f (IO a) -> IO a

instance Exec Teletype where
  execAlgebra (GetChar f)    = Prelude.getChar >>= f
  execAlgebra (PutChar c io) = Prelude.putChar c >> io

instance Exec Filesystem where
  execAlgebra (ReadFile path f)    = Prelude.readFile path >>= f
  execAlgebra (WriteFile path str io) = Prelude.writeFile path str >> io

instance (Exec f, Exec g) => Exec (f :+: g) where
  execAlgebra (Inl x) = execAlgebra x
  execAlgebra (Inr y) = execAlgebra y

exec :: Exec f => Term f a -> IO a
exec = foldTerm return execAlgebra


putCharMy :: (Teletype :<: f) => Char -> Term f ()
putCharMy ch = injectM (PutChar ch (Pure ()))

getCharMy :: (Teletype :<: f) => Term f Char
getCharMy = injectM (GetChar Pure)

readFileMy :: (Filesystem :<: f) => FilePath -> Term f String
readFileMy path = injectM (ReadFile path Pure )

writeFileMy :: (Filesystem :<: f) => FilePath -> String -> Term f ()
writeFileMy path str = injectM (WriteFile path str (Pure ()))



cat :: FilePath -> Term (Teletype :+: Filesystem) ()
cat path = do
  file <- readFileMy path
  mapM putCharMy file
  return ()

-- Let's run
main :: IO ()
main = do
  putStrLn "Part1"
  putStrLn $ render' example1 ++ " => " ++ show   (eval' example1)
  putStrLn "Part3"
  putStrLn $ pretty example2  ++ " => " ++ show   (eval example2)
  putStrLn $ pretty example3  ++ " => " ++ show   (eval example3)
  putStrLn "Part5"
  putStrLn $ pretty example4  ++ " => " ++ show   (eval example4)
  putStrLn $ pretty example5  ++ " => " ++ show   (eval example5)

  putStrLn $ pretty example4  ++ " => " ++ pretty (tryDistr example4)
  putStrLn $ pretty example5  ++ " => " ++ pretty (tryDistr example5)
  putStrLn $ pretty example6  ++ " => " ++ pretty (tryDistr example6)

  putStrLn "Part6"
  putStrLn $ " => " ++ show (run tick (Mem 4))
  putStrLn $ " => " ++ show (run tick (Mem 2))
  putStrLn "Part7"
  exec $ cat "test.txt"
