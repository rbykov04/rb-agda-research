
# 1
1 - I need start simple agda project.

# 2
I understand about nothing in agda. But who can stop me?

I will play with:
Hefty Algebras: Modular Elaboration of Higher-Order Algebraic Effects
https://dl.acm.org/doi/10.1145/3571255
https://github.com/heft-lang/POPL2023/tree/v1.0


# 3 A few weeks later
I rebuild Hefty and Free "engine" to create effects.
I know smth about agda.
I have more question then answers.
And I feel from now I can move forward with sensible steps. 

Anyway, where am I?
I have finished 3.4 Hefty Algebras of [^1].
I can build simple programs with effects.
I understand litle.

I need a plan.

Let's build todo list:

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
- To separate "stdlib" to special folder
- To separate effects to their own files
- To build examples
- To research how hefty works

Other
- To build report

# 4. Separate stdlib file to folder

I copied a lot of stdlib functions from stdlib. 
I couldn't manage to enable stdlib and I just copied functions with hands. :D

I don't want to use stdlib this time.
Let's just separate functions.

Done:
```
Mystdlib
├── IO.agda       - IO
├── Mystdlib.agda - All function
└── Universe.agda - Universe there :D
```

# 5. playing with case op

I have this code:
```
alg eCatch (catch t) fork k = do
        (just x) <- (# givenHandle hThrow (fork true) tt)
            where -- magic: it is so unintuitive
                nothing -> do
                            x <- (fork false)
                            k x
        k x
  where open import Free using (_>>=_; _>>_)
```
What is here???

Let's play with:

```
case_of_ : {A B : Type} -> A -> (A -> B) -> B
case x of f = f x
```

Done:
```
alg eCatch (catch t) fork k = do
        res <- (# givenHandle hThrow (fork true) tt)
        case res of \ where
            (just x) -> k x
            nothing -> do
                x <- (fork false)
                k x
  where open import Free using (_>>=_; _>>_)
```

# 6 
I hacked agda compiler

```
instance Pretty HS.DataOrNew where
  pretty HS.DataType = "data"
  --pretty HS.NewType  = "newtype"
  pretty HS.NewType  = "data"
```

```
  /home/rbykov/dev/opensource/agda/src/full/Agda/Compiler/MAlonzo:
  -rw-rw-r-- 1 rbykov rbykov 2,8K мар  7 16:22 Coerce.hs
  -rw-rw-r-- 1 rbykov rbykov  48K мар  7 16:22 Compiler.hs
  -rw-rw-r-- 1 rbykov rbykov 2,3K мар  7 16:22 Encode.hs
  -rw-rw-r-- 1 rbykov rbykov 9,0K мар  7 16:22 HaskellTypes.hs
  -rw-rw-r-- 1 rbykov rbykov  13K мар  7 16:22 Misc.hs
  -rw-rw-r-- 1 rbykov rbykov 9,0K мар  7 16:22 Pragmas.hs
  -rw-rw-r-- 1 rbykov rbykov 7,9K мар 15 20:15 Pretty.hs <---------------- here
  -rw-rw-r-- 1 rbykov rbykov  15K мар  7 16:22 Primitives.hs
  -rw-rw-r-- 1 rbykov rbykov 3,0K мар  7 16:22 Strict.hs

```


[^1]: Hefty Algebras: Modular Elaboration of Higher-Order Algebraic Effects
https://dl.acm.org/doi/10.1145/3571255
https://github.com/heft-lang/POPL2023/tree/v1.0

[^2]: Wouter Swierstra. 2008. Data types à la carte. J. Funct. Program. 18, 4 (2008), 423–436. https://doi.org/10.1017/S0956796808006758
