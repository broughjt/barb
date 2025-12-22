#import("../../../../../library/template.typ"): *

#show: template

```agda
module Base.Universe.Core where
```

= Agda universe level <note:f91454f0-eb29-4087-8099-8f428cb6a11e>

In Agda, a *universe level* is an index into a hierarchy of type
universes. There is a zeroth level and a successor function that takes one level
to the next in the hierarchy. You can also take the join of two universe levels.

```agda
open import Agda.Primitive public
  using (Level; _⊔_)
  renaming (lzero to zero; lsuc to successor; Set to Type)
```
