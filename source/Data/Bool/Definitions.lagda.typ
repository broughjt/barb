#import("../../../../../library/template.typ"): *

#show: template

```agda
module Data.Bool.Definitions where

open import Base.Universe.Core
open import Data.Bool.Core as Bool
open import Data.Empty.Core
open import Data.Unit.Core
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

= Observational equality on booleans <note:3a2749a4-1b34-4bd5-8821-271a987b029a>

Following #cite(<rijke2025>, form: "prose", supplement: "exer. 6.2(a)"), we
define *observational equality on booleans*, which is a dedicated notion of
equality for booleans, used to characterize the boolean identity types and show
that booleans have decidable equality.

```agda
Equal : 𝟐 → 𝟐 → Type zero
Equal false false = 𝟏
Equal false true = 𝟎
Equal true false = 𝟎
Equal true true = 𝟏
```
