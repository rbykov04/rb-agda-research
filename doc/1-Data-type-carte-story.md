# Data-type-la-carte

# 1. Data type la carte: Motivation
There is one part of [^1] (most hardest part for me): 
**2.2 Row Insertions and Smart Constructors**

The problem is simple:

From this code:
```
hello-throw : Free (Output ⊕ Throw) A
hello-throw = impure (inj1 (out "Hello")) ( _ →
              impure (inj1 (out " world!")) ( _ →
              impure (inj2 throw) ⊥-elim))
```

To this:

```
hello-throw1 : {| Δ ∼ Output ◮ Δ1 |} → {| Δ ∼ Throw ◮ Δ2 |} → Free Δ A
hello-throw1 = do `out "Hello"; `out " world!"; throw
```

But how?

```
To reduce syntactic overhead, we use row insertions and smart constructors.  [Swierstra 2008].
```

Look at this:
```
data _∼_▸_ : Effect → Effect → Effect → Set₁ where
  insert :                 (Δ₀ ⊕ Δ′) ∼ Δ₀ ▸ Δ′
  sift   : (Δ ∼ Δ₀ ▸ Δ′) → ((Δ₁ ⊕ Δ) ∼ Δ₀ ▸ (Δ₁ ⊕ Δ′))

‵out : ⦃ Δ ∼ Output ▸ Δ′ ⦄ → String → Free Δ ⊤
‵out ⦃ w ⦄ s = impure (inj▸ₗ (out s)) (pure ∘ proj-ret▸ₗ ⦃ w ⦄)
```

It irritates me a lot!

I need to work on data type la carte [^2].


# 2. Data type la carte: Overview and Start
The article [^2] is not so long: 14 pages.
And it is about Haskell. 

My plan:

1. Read and repeat in Haskell
2. Repeat again in agda 

So Let's create folder for data typa la carte research.

Done:
```
 ~/dev/github/rb-agda-research   main ●  tree DataTypeLaCarte 
DataTypeLaCarte
├── interactive.sh
├── Main.hs
├── Makefile
└── Readme.md
```

# 3. Data type la carte: part 1 and part2
I started reading atricle and this is the first point.

To solve problem fixed problem modulatiry

We start from this:
```
data Expr = Val Int 
           | Add Expr Expr

```

Then we make type Expr "open".

```
data Expr f  = In (f (Expr f))
```

And make constructors to data type
```
data Val e   = Val Int
type IntExpr = Expr Val

data Add e   = Add e e
type AddExpr = Expr Add
```
From now we can add as many extra "constructors" as we want without changing data Expr.

And to collect them we will use this magic:

```
data (f :+: g) e = Inl (f e) | Inr (g e)
```

Actually it is Either type (or Sum type).

And we have actually the same:


```
data Expr = Val Int 
           | Add Expr Expr
```
But now. it is "open" or "unfixed". We can add new "constructors" on flight.
Amazing and crazy!

But we should pay:

```
example2 :: Expr (Val :+: Add)
example2 = In (Inr (Add (In (Inl (Val 118)))(In (Inl (Val 1219)))))
```

It is Crazy.
And how do we can eval this??


[^1]: Hefty Algebras: Modular Elaboration of Higher-Order Algebraic Effects
https://dl.acm.org/doi/10.1145/3571255
https://github.com/heft-lang/POPL2023/tree/v1.0

[^2]: Wouter Swierstra. 2008. Data types à la carte. J. Funct. Program. 18, 4 (2008), 423–436. https://doi.org/10.1017/S0956796808006758


