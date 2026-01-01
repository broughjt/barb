#import("../../../../library/template.typ"): *

#show: template

```agda
module Data.Empty where

open import Base.Universe.Core
```

= Empty type <note:9d7cf197-7f2a-4633-aa63-1c9df1429a13>
 
Following #cite(<rijke2025>, form: "prose", supplement: "def. 4.3.1"), the
*empty type*, denoted $emptyType$, is the type without any
#link("note://367095ff-9cce-417f-a059-9c0290d0ca99")[constructors] which
satisfies the #link("note://367095ff-9cce-417f-a059-9c0290d0ca99")[induction
principle] that for any
#link("note://b05d0e2e-b6ab-45ab-9277-9559f4ee5e1f")[type family] $P(x)$ indexed
by $x ofType emptyType$, there is a
#link("note://516e852c-8a6d-4c43-8b5a-a64c3c603926")[section]

$
    induction0 : piType(x, emptyType) P(x).
$

```agda
data 𝟎 : Type zero where

induction : {i : Level} {P : 𝟎 → Type i} →
            ((x : 𝟎) → P x)
induction ()

recursion : {i : Level} {A : Type i} → (𝟎 → A)
recursion = induction
```

#link("note://ae121b5e-c986-4f89-a3eb-ecac84255fa9")[This note] offers
commentary on understanding the induction principle for the empty type.
