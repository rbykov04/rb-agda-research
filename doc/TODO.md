# TODO And Questions

The article todo:
- [^1] 4 VERIFYING ALGEBRAIC LAWS FOR HIGHER-ORDER EFFECTS
    - No chances to understand 
- [^1] Example: 5.2 Optionally Transactional Exception Catching
    - Hard one.
- [^1] Example: 5.4 Concurrency
    - Hard one.
- [^1] Example: 5.3 Logic Programming
    - Simple one.
- [^1] Example: 5.1 Lambda as a Higher-Order Operation
    - No chances to understand 

The source code todo:
- DONE: To separate "stdlib" to special folder
- To separate effects to their own files
    - Done Catch
    - Out
    - Throw
- To build examples
- To research how hefty works
    - play with effects without smart constuctors
- to chose dir structure where place effects 


Other
- To build report

Agda-lang
- DONE case_of_ use in Catch effect 
- How does case of work? We can declare lambda with where??
```
alg eCatch (catch t) fork k = do
        res <- (# givenHandle hThrow (fork true) tt)
        case res of \ where
            (just x) -> k x
            nothing -> do
                x <- (fork false)
                k x
```


Theory:
- What is "Universe" 
    - What is "a universe of types [Martin-Löf 1984]."
    - What does "syntactic type TY" mean?
    - Mystdlib/Universe
- Read "Data type la carte"
    - Done haskell version
    - write a small report about article
    - repeat in agda
    - Tmp.hs - play with Class and Instances more
    - Change infix operator to casual type name and rebuild system
        - :<:
        - :+:
    - Read Next "These monads are known as free monads (Awodey, 2006).""
        Awodey, S. (2006) Category Theory. Oxford Logic Guides, vol. 49. Oxford: Oxford University Press.
    - Read Wadler https://homepages.inf.ed.ac.uk/wadler/papers/expression/expression.txt
    - 8 Discussion - I need to unfold this to extra todos



- What is Functor?
    - maybe play with this: https://stackoverflow.com/questions/13134825/how-do-functors-work-in-haskell
    
haskell
- -XOverlappingInstances is deprecated:
```
Main.hs:1:14: warning: [-Wdeprecated-flags]
    -XOverlappingInstances is deprecated: instead use per-instance pragmas OVERLAPPING/OVERLAPPABLE/OVERLAPS
  |
```
- Read about Haskell Stdlib: Monad and applicative


## Data Type la carte

think:
```
data Term f a =
Pure a
| Impure (f (Term f a))

In general, a structure is called free when it is left-adjoint to a forgetful functor.
In this specific instance, the Term data type is a higher-order functor that maps
a functor f to the monad Term f ; this is illustrated by the above two instance
definitions. This Term functor is left-adjoint to the forgetful functor from monads
to their underlying functors.

All left-adjoint functors preserve coproducts. In particular, computing the coproduct of two free monads reduces to computing the coproduct of their underlying
functors, which is exactly what we achieved in Section 2. Throughout this section,
we will exploit this property to define monads modularly.
```


- Add bib tex file


- Add
flags:
  --erased-matches
  --exact-split
  --guardedness
  --hidden-argument-puns
  --no-import-sorts
  --postfix-projections
  --qualified-instances

  -Werror
  -WnoUnsupportedIndexedMatch
