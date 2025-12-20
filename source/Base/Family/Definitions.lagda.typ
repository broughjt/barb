#import("../../../../../library/template.typ"): *

#show: template

```agda
module Base.Family.Definitions where

open import Base.Function.Negation
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

= Irreflexive <note:088c9e40-5313-4e02-96df-58368e796ebe>
 
A homogeneous binary #link("note://b05d0e2e-b6ab-45ab-9277-9559f4ee5e1f")[type
family] $R ofType A -> A -> cal(U)$ over a type $A$ is *irreflexive* if $R(x,
x)$ #link("note://16ffba35-7712-4eb7-8902-0812e529aa16")[is empty] for every $x
ofType A$.

```agda
Irreflexive : {i j : Level} {A : Type i} → 
              (A → A → Type j) → Type (i ⊔ j)
Irreflexive {A = A} R = (x : A) → ¬ R x x
```

= Symmetric <note:ef9aa02f-8f36-46f5-ab3b-829123f2a139>
 
A homogeneous binary #link("note://b05d0e2e-b6ab-45ab-9277-9559f4ee5e1f")[type
family] $R ofType A -> A -> cal(U)$ over a type $A$ is *symmetric* if there
$R(x, y)$ implies $R(y, x)$ for all $x, y ofType A$.

```agda
Symmetric : {i j : Level} {A : Type i} →
            (A → A → Type j) → Type (i ⊔ j)
Symmetric {A = A} R = {x y : A} → R x y → R y x
```

= Transitive <note:8ee19084-9149-4088-8b11-e921bd2d7e4c>

A homogeneous binary #link("note://b05d0e2e-b6ab-45ab-9277-9559f4ee5e1f")[type
family] $R ofType A -> A -> cal(U)$ over a type $A$ is *transitive* if for all
$x, y, z ofType A$, if $R(x, y)$ and $R(y, z)$ then $R(x, z)$.

```agda
Transitive : {i j : Level} {A : Type i} →
             (A → A → Type j) → Type (i ⊔ j)
Transitive {A = A} R = {x y z : A} → R x y → R y z → R x z
```
