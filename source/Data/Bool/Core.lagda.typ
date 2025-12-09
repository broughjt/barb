#import("../../../../../library/template.typ"): *

#show: template

```agda
module Data.Bool.Core where

open import Base.Universe
```

= Type of booleans <note:78e3004d-88e7-45e5-8d4d-da76962195f3>
 
The type of *booleans*, written $Bool$, consists of values for true and false
@rijke2025[exer. 4.2]. The
#link("note://367095ff-9cce-417f-a059-9c0290d0ca99")[induction principle] for
booleans states that given any
#link("note://b05d0e2e-b6ab-45ab-9277-9559f4ee5e1f")[type family] $P ofType Bool
-> cal(U)$, there is a function
$
    induction_(Bool) ofType P(bfalse) -> P(btrue) -> piType(x, Bool) P(x)
$
satisfying the #link("note://367095ff-9cce-417f-a059-9c0290d0ca99")[computation
rules]
$
    induction_(Bool)(p, q, btrue) & dot(eq) p, \
    induction_(Bool)(p, q, bfalse) & dot(eq) q.
$
In other words, the induction principle for booleans asserts that to construct a
section of an arbitrary type family over the booleans, it suffices to provide
values for $btrue$ and $bfalse$.

```agda
data 𝟐 : Type zero where
  false true : 𝟐

induction : {i : Level} {P : 𝟐 → Type i} →
            P false → P true → ((x : 𝟐) → P x)
induction p _ false = p
induction _ q true = q

recursion : {i : Level} {A : Type i} →
            A → A → (𝟐 → A)
recursion = induction
```
