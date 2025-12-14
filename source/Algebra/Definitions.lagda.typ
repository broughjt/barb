#import("../../../../library/template.typ"): *

#show: template

```agda
module Algebra.Definitions where

open import Base.Identity.Core
open import Base.Universe
```

= Associative <note:9affcc46-5cf0-4627-b909-80ec3cba8a2d>
 
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

= Commutative <note:22261946-d41d-4db3-849d-0511c26b0dea>

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
