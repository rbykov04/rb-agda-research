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
- To build examples
- To research how hefty works
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
    



