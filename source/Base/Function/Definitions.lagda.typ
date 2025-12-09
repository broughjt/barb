#import("../../../../../library/template.typ"): *

#show: template

```agda
module Base.Function.Definitions where

open import Base.Universe
open import Data.Sigma.Core
```

= Logical biconditional <note:27061ddb-2091-46c1-8752-21db2ab57f44>

Under the Curry-Howard interpretation, logical implication $P ==> Q$ is
expressed as a function type $P -> Q$, where $P$ and $Q$ are types. Therefore,
we express the notion of the *logical biconditional*, or *biimplication*, or
*logical equivalence* between two types $A$ and $B$ as the
#link("note://23a01b78-e433-4a66-8915-bfda82ee149a")[product] $(A -> B) times (B
-> A)$ @rijke2025[exer. 4.3].

```agda
_↔_ : {i j : Level} (A : Type i) (B : Type j) → Type (i ⊔ j)
A ↔ B = (A → B) × (B → A)
```
