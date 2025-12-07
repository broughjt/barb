#import("../../../../library/template.typ"): *

#show: template

```agda
module Data.Unit where

open import Foundation.Universe
```

= Unit type <note:fe0ba530-46e9-4031-83bb-330db4d12b4e>
 
The *unit type*, denoted $unitType$, is the type equipped with a single
#link("note://367095ff-9cce-417f-a059-9c0290d0ca99")[constructor] $star ofType
unitType$, satisfying the
#link("note://367095ff-9cce-417f-a059-9c0290d0ca99")[induction principle] that
for any #link("note://b05d0e2e-b6ab-45ab-9277-9559f4ee5e1f")[family of types]
$P(x)$ indexed by $x ofType unitType$, there is a function

$
    induction1 ofType P(star) -> piType(x, unitType) P(x)
$

satisfying the #link("note://367095ff-9cce-417f-a059-9c0290d0ca99")[computation
rule]

$
    induction1(p, star) dot(eq) p
$

for any $p ofType P(star)$ @rijke2025[def. 4.2.1].

```agda
data 𝟏 : Type zero where
  ⋆ : 𝟏

induction : {i : Level} {P : 𝟏 → Type i} →
            P ⋆ → ((x : 𝟏) → P x)
induction p ⋆ = p
```
