#import("../../../../../library/template.typ"): *

#show: template

```agda
module Data.Empty.Properties where

open import Base.Truncation.Definitions
open import Base.Universe.Core
open import Data.Empty.Core as Empty
```

= Empty type is a proposition <note:32deb8dc-8fac-48c4-929e-6213aa79da70>
 
#lemma(supplement: cite_link(<rijke2025>, "Rijke 2025, ex. 12.1.2"))[
    The #link("note://9d7cf197-7f2a-4633-aa63-1c9df1429a13")[empty type] is a
    #link("note://07db70c3-0206-4a29-a7c1-77d208539cec")[proposition].
]
#proof[
    Holds vacuously.
]

```agda
emptyIsProposition : IsProposition 𝟎
emptyIsProposition = Empty.induction
```
