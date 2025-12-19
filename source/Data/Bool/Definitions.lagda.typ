#import("../../../../../library/template.typ"): *

#show: template

```agda
module Data.Bool.Definitions where

open import Base.Universe
open import Data.Bool.Core as Bool
```

= Boolean operations <note:84ca1018-8448-4ecf-beb0-9bc92b18c914>
 
We define *negation*, *conjunction*, and *disjunction* on
#link("note://78e3004d-88e7-45e5-8d4d-da76962195f3")[booleans] following
#cite(<rijke2025>, form: "prose", supplement: "exer. 4.2").

```agda
!_ : 𝟐 → 𝟐
! true = false
! false = true

infix 3 !_

_&&_ : 𝟐 → 𝟐 → 𝟐
true && x = x
false && _ = false

infixr 7 _&&_

_||_ : 𝟐 → 𝟐 → 𝟐
true || _ = true
false || x = x

infixr 6 _||_
```
