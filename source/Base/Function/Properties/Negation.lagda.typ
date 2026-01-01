#import("../../../../../../library/template.typ"): *

#show: template

```agda
module Base.Function.Properties.Negation where

open import Base.Function.Core
open import Base.Function.Definitions
open import Base.Universe.Core
open import Data.Empty as Empty
```

= The recursion principle for the empty type is an embedding for any codomain <note:2925d5d4-158a-4d10-a9d1-cd1d9559db2c>

#lemma(supplement: cite_link(<rijke2025>, "Rijke 2025, exer. 11.1(a)"))[
    For every type $A$, the
    #link("note://9d7cf197-7f2a-4633-aa63-1c9df1429a13")[recursion principle for
    the empty type]
    $
        recursion_(emptyType) ofType emptyType -> A
    $
    is an #link("note://cce94748-d9b3-4795-a3d8-c698b6dff9dd")[embedding].
]
#proof[
    Holds vacuously.
]

```agda
emptyRecursionIsEmbedding :
  {i : Level} {A : Type i} →
  IsEmbedding $ Empty.recursion {A = A}
emptyRecursionIsEmbedding {i} {A} = Empty.induction
```
