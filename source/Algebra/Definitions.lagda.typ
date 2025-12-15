#import("../../../../library/template.typ"): *

#show: template

```agda
module Algebra.Definitions where

open import Base.Identity.Core
open import Base.Universe
open import Data.Sigma.Core
```

= Associativity <note:9affcc46-5cf0-4627-b909-80ec3cba8a2d>
 
A binary operator $- dot.op - ofType A -> A -> A$ is *associative* if the
equation
$
    (x dot.op y) dot.op z = x dot.op (y dot.op z)
$
holds for all $x, y, z ofType A$.

```agda
Associative : {i : Level} {A : Type i} →
              (A → A → A) → Type i
Associative {_} {A} _∙_ = (x y z : A) → (x ∙ y) ∙ z ＝ x ∙ (y ∙ z)
```

= Commutativity <note:22261946-d41d-4db3-849d-0511c26b0dea>

A binary operator $- dot.op - ofType A -> A -> A$ is *commutative* if
$
    x dot.op y = y dot.op x
$
for all $x, y ofType A$.

```agda
Commutative : {i : Level} {A : Type i} →
              (A → A → A) → Type i
Commutative {_} {A} _∙_ = (x y : A) → x ∙ y ＝ y ∙ x
```

= Distributivity <note:950bc0dc-2afc-4bd1-beab-ad2895783cc5>
 
Let $dot.op, + ofType A -> A -> A$ be binary operators on a type $A$. The
operation $dot.op$ is *left-distributive over* $+$ if
$
    x dot.op (y + z) = x dot.op y + x dot.op z
$
for all $x, y, z ofType A$. Similarly, the operation $dot.op$ is
*right-distributive over* $+$ if
$
    (x + y) dot.op z = x dot.op z + y dot.op z
$
for all $x, y, z ofType A$. The operation $dot.op$ is *distributive over* $+$ if
it is both left- and right-distributive.

```agda
DistributesOverˡ : {i : Level} {A : Type i} →
                   (A → A → A) → (A → A → A) → Type i
DistributesOverˡ {_} {A} _·_ _+_ =
  (x y z : A) → x · (y + z) ＝ (x · y) + (x · z)

DistributesOverʳ : {i : Level} {A : Type i} →
                   (A → A → A) → (A → A → A) → Type i
DistributesOverʳ {_} {A} _·_ _+_ =
  (x y z : A) → (x + y) · z ＝ (x · z) + (y · z)

DistributesOver : {i : Level} {A : Type i} →
                  (A → A → A) → (A → A → A) → Type i
DistributesOver {_} {A} _·_ _+_ =
  (DistributesOverˡ _·_ _+_) × (DistributesOverʳ _·_ _+_)
```
