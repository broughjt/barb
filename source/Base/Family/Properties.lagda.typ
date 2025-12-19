#import("../../../../../library/template.typ"): *

#show: template

```agda
module Base.Family.Properties where

open import Base.Universe
open import Base.Family.Definitions
open import Base.Identity.Core
```

= Canonical map from identity types into reflexive relations <note:d25ccc40-b51e-466f-b87a-59be3acfa38a>

#lemma(label: "11")[
    For each #link("note://7e7a1c6f-6051-4526-83e9-01d030717ea5")[reflexive]
    homogeneous binary #link("note://b05d0e2e-b6ab-45ab-9277-9559f4ee5e1f")[type
    family] $R ofType A -> A -> cal(U)$ over a type $A$, there is a canonical
    map
    $
        piType(x, y, A) x = y -> R(x, y).
    $
]
#proof[
    By #link("note://261490cb-2887-4247-9a83-7f674e3c9651")[path induction], it
    suffices to assume the
    #link("note://261490cb-2887-4247-9a83-7f674e3c9651")[path] is $refl_(x)
    ofType x = x$ and construct an element of $R(x, x)$. We have such an element
    by the assumption that $R$ is reflexive.
]

```agda
＝→reflexive : {i j : Level} {A : Type i} {R : A → A → Type j} →
               Reflexive R →
               {x y : A} → x ＝ y → R x y
＝→reflexive p {x} {x} reflexive = p x
```
