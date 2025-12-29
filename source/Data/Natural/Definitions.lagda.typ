#import("../../../../../library/template.typ"): *

#show: template

```agda
module Data.Natural.Definitions where

open import Base.Universe.Core as Universe hiding (zero; successor)
open import Data.Empty
open import Data.Natural.Core
open import Data.Unit.Core
```

= Natural number addition <note:1be8278b-eb3c-4fc7-8ee4-2e4c9fa92662>

*Addition* on #link("note://600e8ce4-83d2-4a92-9295-ccb0aef05689")[natural
numbers] is defined by recursion on the first argument $n$, iteratively applying
the successor constructor to the second argument $n$ times
@rijke2025[def. 3.2.1].

```agda
_+_ : ℕ → ℕ → ℕ
zero + m = m
successor n + m = successor (n + m)

{-# BUILTIN NATPLUS _+_ #-}

infixl 6 _+_
```

= Natural number multiplication <note:87e01952-e90c-4a12-96db-6906d98f6755>
 
*Multiplication* on #link("note://600e8ce4-83d2-4a92-9295-ccb0aef05689")[natural
numbers] is defined recursively as repeated addition @rijke2025[exer. 3.1(a)].

```agda
_·_ : ℕ → ℕ → ℕ
zero · m = zero
successor n · m = (n · m) + m

{-# BUILTIN NATTIMES _·_ #-}

infixl 7 _·_
```

= Distance function on natural numbers <note:9dd496bb-370e-481c-81ad-1ace2b8f6a29>
 
The *distance function* gives the "symmetric distance" between two natural
numbers @rijke2025[exer. 6.5]. We define using double recursion.

```agda
distance : ℕ → ℕ → ℕ
distance zero zero = zero
distance zero (successor m) = successor m
distance (successor n) zero = successor n
distance (successor n) (successor m) = distance n m
```

= Observational equality of the natural numbers <note:4e056c9c-2c11-4992-9838-3dda731d17fa>

Following #cite(<rijke2025>, form: "prose", supplement: "def. 6.3.1"),
*Observational equality of natural numbers* is a relation which acts as a
dedicated notion of equality for the
#link("note://600e8ce4-83d2-4a92-9295-ccb0aef05689")[natural numbers], in
contrast to general
#link("note://261490cb-2887-4247-9a83-7f674e3c9651")[identity types]. The idea
is that we can use this to characterize the identity types of natural numbers
and then use this characterization to prove useful properties.

We determine whether two natural numbers $n$ and $m$ are observationally equal
by double recursion on $n$ and $m$:

1. If both $n$ and $m$ are zero, then they are observationally equal.
2. If either $n$ is zero and $m dot(eq) s(m')$ for some $m' ofType NN$ or vice
   versa, then $n$ and $m$ are not observationally equal.
3. If both $n dot(eq) s(n')$ and $m dot(eq) s(m')$ for $n', m' ofType NN$, then
   $n$ and $m$ are observationally equal if $n'$ and $m'$ are observationally
   equal.

Because this is the same pattern of recursion used to calculate the
#link("note://9dd496bb-370e-481c-81ad-1ace2b8f6a29")[distance function] on
natural numbers, I have modified Rijke's definition slightly by using
with-abstraction on the result of $distance(n, m)$.

```agda
Equal : ℕ → ℕ → Type Universe.zero
Equal n m with distance n m
... | zero = 𝟏
... | successor k = 𝟎
```
