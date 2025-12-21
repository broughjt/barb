#import("../../../../../library/template.typ"): *

#show: template

```agda
module Data.Unit.Properties where

open import Base.Identity.Core
open import Base.Truncation.Definitions
open import Base.Universe
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
unitContractible : IsContractible 𝟏
unitContractible = pair ⋆ (Unit.induction {P = _＝_ ⋆} reflexive)
```
