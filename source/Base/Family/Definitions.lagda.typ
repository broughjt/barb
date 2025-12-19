#import("../../../../../library/template.typ"): *

#show: template

```agda
module Base.Family.Definitions where

open import Base.Universe
```

= Reflexive <note:7e7a1c6f-6051-4526-83e9-01d030717ea5>
 
A homogeneous binary #link("note://b05d0e2e-b6ab-45ab-9277-9559f4ee5e1f")[type
family] $R ofType A -> A -> cal(U)$ over a type $A$ is *reflexive* if the
#link("note://85839d30-6530-4e54-a8ba-efd1c8709928")[fiber] $R(x, x)$ is
inhabited for every $x ofType A$.

```agda
Reflexive : {i j : Level} {A : Type i} →
            (A → A → Type j) → Type (i ⊔ j)
Reflexive {A = A} R = (x : A) → R x x
```
