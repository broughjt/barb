#import("../../../../../library/template.typ"): *

#show: template

```agda
module Base.Truncation.Definitions where

open import Base.Identity.Core
open import Base.Universe
open import Data.Sigma.Core
```

= Contractible type <note:f817901c-750e-4575-a259-d83730424ade>
 
Following #cite(<rijke2025>, form: "prose", supplement: "def. 10.1.1"), a type
$A$ is *contracitble* if it comes equipped with an element of type
$
    IsContractible(A) := sigmaType(c, A) piType(x, A) c = x.
$
Given a pair $(c, C) ofType IsContractible(A)$, we refer to $c ofType A$ as the
*center of contraction* of $A$, and we refer to $C ofType piType(x, A) c = x$ as
the *contraction* of $A$.

```agda
IsContractible : {i : Level} →
                 Type i → Type i
IsContractible A = Σ A (λ c → (x : A) → c ＝ x)
```
