#import("../../../../../library/template.typ"): *

#show: template

```agda
module Data.Bool.Properties where

open import Base.Function.Core
open import Base.Function.Definitions
open import Base.Identity.Core
open import Base.Universe
open import Data.Bool.Core as Bool
open import Data.Bool.Definitions as Bool
```

= Boolean double negation homotopic to identity <note:547845e0-625b-4444-9b32-9a66352293d2>
 
#lemma(supplement: cite_link(<rijke2025>, "Rijke 2025, ex. 9.1.3"))[
    There is a #link("note://3cb1b8ca-2a77-4c8a-b726-ed8f10dfd208")[homotopy]
    $
        (lambda x . ! x) compose (lambda x . ! x) ~ id_(Bool)
    $
    between double #link("note://84ca1018-8448-4ecf-beb0-9bc92b18c914")[boolean
    negation] and the
    #link("note://efea6413-096d-4249-8ef0-a4de74fcee13")[identiy map].
]
#proof[
    The cases for both $btrue$ and $bfalse$ hold
    #link("note://84ca1018-8448-4ecf-beb0-9bc92b18c914")[definitionally].
]

```agda
!!∼identity : (!_ ∘ !_) ∼ identity
!!∼identity false = reflexive
!!∼identity true = reflexive
```

See #link("note://78e3004d-88e7-45e5-8d4d-da76962195f3")[Type of booleans].
