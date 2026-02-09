#import("../../../../../../library/template.typ"): *

#show: template

```agda
module Base.Truncation.Properties.Proposition where

open import Base.Truncation.Definitions
open import Base.Truncation.Properties.Contractible
open import Base.Universe.Core
```

= Contractible types are propositions <note:667afa3d-7138-4598-a297-4e02d07478ae>
 
#corollary(
    label: "86",
    supplement: cite_link(<rijke2025>, "Rijke 2025, ex. 12.1.2")
)[
    Every #link("note://f817901c-750e-4575-a259-d83730424ade")[contractible]
    type is a #link("note://07db70c3-0206-4a29-a7c1-77d208539cec")[proposition].
]
#proof[
    This is just a restatement of
    #link("note://1d8b9cbe-0517-4ca7-840a-d9601bedde8e")[Lemma 85], now with
    language of
    #link("note://07db70c3-0206-4a29-a7c1-77d208539cec")[propositions].
]

```agda
isContractible→isProposition :
  {i : Level} {A : Type i} →
  IsContractible A → IsProposition A
isContractible→isProposition {A} = isContractible→＝-isContractible
```
