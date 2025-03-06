# This folder to save agda lang stuff

Q: What is INLINE and NOINLINE in haskell and agda ?
https://hackage.haskell.org/package/ghc-internal-9.1201.0/docs/src/GHC.Internal.Base.html#%2B%2B
```
-- >>> [3, 2, 1] ++ []
-- [3,2,1]
(++) :: [a] -> [a] -> [a]
{-# NOINLINE [2] (++) #-}
```
