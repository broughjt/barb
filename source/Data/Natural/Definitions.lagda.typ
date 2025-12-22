#import("../../../../../library/template.typ"): *

#show: template

```agda
module Data.Natural.Definitions where

open import Base.Universe.Core hiding (zero; successor)
open import Data.Natural.Core
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
