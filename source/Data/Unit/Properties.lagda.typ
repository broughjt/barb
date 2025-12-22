#import("../../../../../library/template.typ"): *

#show: template

```agda
module Data.Unit.Properties where

open import Base.Identity.Core
open import Base.Truncation.Definitions
open import Base.Universe.Core
open import Data.Sigma.Core
open import Data.Unit.Core as Unit
```

= Unit type is contractible <note:2bd735ed-2f78-4b32-8b6f-77e9a5c57573>
 
#lemma(supplement: cite_link(<rijke2025>, "Rijke 2025, ex. 10.1.3"))[
    The #link("note://fe0ba530-46e9-4031-83bb-330db4d12b4e")[unit type] is
    #link("note://f817901c-750e-4575-a259-d83730424ade")[contractible].
]
#proof[
    Take $star ofType unitType$ as the
    #link("note://f817901c-750e-4575-a259-d83730424ade")[center of
    contraction]. To define a
    #link("note://f817901c-750e-4575-a259-d83730424ade")[contraction] $piType(x,
    unitType) star = x$, apply the
    #link("note://fe0ba530-46e9-4031-83bb-330db4d12b4e")[induction principle for
    the unit type] using the family $P ofType unitType -> cal(U)$ given by $P(x)
    := star = x$. Then it suffices to provide an element of $P(star)$, for which
    we just take $refl_(star)$.
]

```agda
unitIsContractible : IsContractible 𝟏
unitIsContractible = pair ⋆ (Unit.induction {P = _＝_ ⋆} reflexive)
```

= Unit type satisfies singleton induction <note:bcb4a010-3314-44da-a984-9d2d0f24a0f1>
 
#lemma(supplement: cite_link(<rijke2025>, "Rijke 2025, ex. 10.2.2"))[
    The #link("note://fe0ba530-46e9-4031-83bb-330db4d12b4e")[unit type]
    satisfies #link("note://2a65336f-3db1-411e-869f-9c87a18d408a")[singleton
    induction].
]
#proof[
    Take the distinguished element to be $star ofType unitType$. Let $B$ be a
    #link("note://b05d0e2e-b6ab-45ab-9277-9559f4ee5e1f")[type family] over the
    #link("note://fe0ba530-46e9-4031-83bb-330db4d12b4e")[unit type]. We must
    exhibit a function
    $
        induction_(s)^(star) ofType B(star) -> (piType(x, unitType) B(x))
    $
    together with a
    #link("note://3cb1b8ca-2a77-4c8a-b726-ed8f10dfd208")[homotopy]
    $
        evaluate_(star) compose induction_(s)^(star) ~ id_B(star).
    $

    Define $induction_(s)^(star)$ to be the
    #link("note://fe0ba530-46e9-4031-83bb-330db4d12b4e")[induction principle for
    the unit type]. By the definition of the
    #link("note://ac0a22e1-3510-4129-ab02-d0f95da4a48c")[evaluation function],
    constructing the homotopy amounts to constructing a path
    $
        induction1(y, star) = y
    $
    for each $y ofType B(star)$. This holds
    #link("note://a0baf580-5da2-4328-bfbd-202bedf37747")[judgementally] by the
    #link("note://fe0ba530-46e9-4031-83bb-330db4d12b4e")[computation rule for
    the unit type]. Hence the required homotopy is given pointwise by
    #link("note://261490cb-2887-4247-9a83-7f674e3c9651")[reflexivity],
    completing the proof.
]

Note, this proof essentially recounts the description given in
#link("note://5c363e12-3c53-4145-9b22-985fd2af9d7b")[Understanding the
definition of singleton induction].

```agda
unitIsSingleton : {i j : Level} → IsSingleton {j = j} 𝟏
unitIsSingleton =
  pair ⋆
       (λ B → pair (Unit.induction {P = B})
                   (λ y → reflexive))
```
