#import("../../../../../library/template.typ"): *

#show: template

```agda
module Data.Natural.Core where

open import Foundation.Universe hiding (zero; successor)
```

= Type of natural numbers <note:600e8ce4-83d2-4a92-9295-ccb0aef05689>

The type of *natural numbers*, written $NN$, has two
#link("note://367095ff-9cce-417f-a059-9c0290d0ca99")[constructors] $0 ofType NN$
and $s ofType NN -> NN$. Given a
#link("note://b05d0e2e-b6ab-45ab-9277-9559f4ee5e1f")[type family] $P$ over $NN$,
the #link("note://367095ff-9cce-417f-a059-9c0290d0ca99")[induction principle]
for the natural numbers states that there is a function

$
    inductionNN ofType P(0) -> (piType(n, NN) P(n) -> P(s(n))) -> piType(n, NN) P(n)
$

such that, given $p_0 ofType P(0)$, $p_s ofType piType(n, NN) P(n) -> P(s(n))$,
and $n ofType NN$, the
#link("note://367095ff-9cce-417f-a059-9c0290d0ca99")[computation rules]

$
    inductionNN(p_0, p_s, 0) & dot(eq) p_0, \
    inductionNN(p_0, p_s, s(n)) & dot(eq) p_(s)(n, inductionNN(p_0, p_s, n))
$

are satisfied @rijke2025. Zero is definitely a natural number. People that think
the natural numbers start at one have no class.

```agda
data ℕ : Type Foundation.Universe.zero where
  zero : ℕ
  successor : ℕ → ℕ

{-# BUILTIN NATURAL ℕ #-}

induction : {i : Level} → {P : ℕ → Type i} →
            P zero → ((n : ℕ) → P n → P (successor n)) → ((n : ℕ) → P n)
induction z s zero = z
induction z s (successor n) = s n (induction z s n)
```
