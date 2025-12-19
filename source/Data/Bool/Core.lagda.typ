#import("../../../../../library/template.typ"): *

#show: template

```agda
module Data.Bool.Core where

open import Base.Universe
```

= Type of booleans <note:78e3004d-88e7-45e5-8d4d-da76962195f3>
 
Following #cite(<rijke2025>, form: "prose", supplement: "exer. 4.2"), the type
of *booleans*, written $Bool$, consists of values for true and false. The
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
#link("note://516e852c-8a6d-4c43-8b5a-a64c3c603926")[section] of an arbitrary
type family over the booleans, it suffices to provide values for $btrue$ and
$bfalse$.

Note that the traditional `if b then x else y` construct is just nice
syntax sugar for the recursion principle for booleans.

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

if_then_else_ : {i : Level} {A : Type i} →
                𝟐 → A → A → A
if_then_else_ b x y = recursion y x b

infix 0 if_then_else_
```
