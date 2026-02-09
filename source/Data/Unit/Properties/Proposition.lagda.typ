#import("../../../../../../library/template.typ"): *

#show: template

```agda
module Data.Unit.Properties.Proposition where

open import Base.Truncation.Definitions
open import Base.Truncation.Properties.Proposition
open import Data.Unit.Core
open import Data.Unit.Properties.Core
```

= Unit type is a proposition <note:eb4d2838-c1e2-491d-a78d-f126cae0e134>

#corollary(supplement: cite_link(<rijke2025>, "Rijke 2025, ex. 12.1.2"))[
    The #link("note://fe0ba530-46e9-4031-83bb-330db4d12b4e")[unit type] is a
    #link("note://07db70c3-0206-4a29-a7c1-77d208539cec")[proposition].
]
#proof[
    Apply #link("note://667afa3d-7138-4598-a297-4e02d07478ae")[Corollary 86] to
    #link("note://2bd735ed-2f78-4b32-8b6f-77e9a5c57573")[Lemma 87].
]
 
```agda
unitIsProposition : IsProposition 𝟏
unitIsProposition = isContractible→isProposition unitIsContractible
```
