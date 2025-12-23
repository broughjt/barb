#import("../../../../../../library/template.typ"): *

#show: template

```agda
module Base.Universe.Properties.Lift where

open import Base.Function.Core
open import Base.Function.Definitions
open import Base.Function.Properties.Equivalence
open import Base.Identity.Core
open import Base.Universe.Core
open import Base.Universe.Lift
open import Data.Sigma.Core
```

= Types are equivalent to their universe lifted counterparts <note:9c9c665a-6b50-45fe-9c02-2fb2f75a5efd>

#lemma[
    The universe #link("note://b4f1235d-278b-497d-98f2-c215d1cd2cf4")[lifting]
    and #link("note://95201e7f-ee8c-474a-bc12-ad6dfcafa44a")[lowering]
    operations are
    #link("note://32c2ca55-63ba-411b-9052-676a51fd16a1")[inverses].
]
#proof[
]


```agda
liftLowerInverse : {i j : Level} {A : Type i} →
                   Inverse {A = A} {B = Lift j A} lift lower
liftLowerInverse {i} {j} {A} = pair H K
  where
  H : lower {j = j} ∘ lift ∼ identity {_} {A = A}
  H x = reflexive

  K : lift ∘ lower ∼ identity {_} {Lift j A}
  K (lift x) = reflexive

liftIsEquivalence : {i : Level} {A : Type i}
                    (j : Level) →
                    IsEquivalence (lift {j = j} {A = A})
liftIsEquivalence j =
  hasInverse→isEquivalence (pair lower liftLowerInverse)

lowerIsEquivalence : {i : Level} {A : Type i}
                     (j : Level) →
                     IsEquivalence (lower {j = j} {A = A})
lowerIsEquivalence j =
  hasInverse→isEquivalence
    (pair lift
          (inverseInverse lift lower liftLowerInverse))

lift≃ : {i j : Level} {A : Type i} →
        A ≃ Lift j A
lift≃ {j = j} = pair lift (liftIsEquivalence j)
```
