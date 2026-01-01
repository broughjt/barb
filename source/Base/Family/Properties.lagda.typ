#import("../../../../../library/template.typ"): *

#show: template

```agda
module Base.Family.Properties where

open import Base.Universe.Core
open import Base.Family.Definitions
open import Base.Identity.Core as Identity
```

= Canonical map from identity types into reflexive relations (version 2, latest) <note:d25ccc40-b51e-466f-b87a-59be3acfa38a>

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
    Fix $x ofType A$. By
    #link("note://261490cb-2887-4247-9a83-7f674e3c9651")[path induction], it
    suffices to provide an element of $R(x, x)$, which we have by the
    assumption that $R$ is a
    #link("note://7e7a1c6f-6051-4526-83e9-01d030717ea5")[reflexive family].
]

This is the second version of this note (previous version
#link("note://c233adf4-3443-4189-ae30-b1bf5e3827e1")[here]). I realized that
this lemma is literally nothing more than a special case of path induction, and
I wanted my proof to reflect this explicitly. Compared to the previous version,
I changed the Agda proof to use `induction` instead of pattern matching so that
I could make the type family $P$ explicit, and then I adjusted the paper proof
to match.

```agda
＝→reflexive :
  {i j : Level} {A : Type i} {R : A → A → Type j} →
  Reflexive R →
  {x y : A} → x ＝ y → R x y
＝→reflexive {R = R} p {x} {y} =
  Identity.induction {P = λ y p → R x y} (p x) y
```
