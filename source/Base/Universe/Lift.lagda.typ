#import("../../../../../library/template.typ"): *

#show: template

```agda
module Base.Universe.Lift where

open import Base.Function.Core
open import Base.Universe.Core
```

= Universe lifting <note:b4f1235d-278b-497d-98f2-c215d1cd2cf4>
 
Universes are not cummulative in Agda, so we define an explicit *universe
lifting* type, which "lifts" a type from its given universe to any higher
universe. Specifically, given a type $A ofType cal(U)_(i)$ and another universe
$cal(U)_(j)$, the type $Lift(A)$ is an inductive with equipped with a
constructor $lift ofType A -> Lift(A)_(cal(U)_(i union.sq j))$.

```agda
data Lift (j : Level) {i : Level} (A : Type i) : Type (i ⊔ j) where
  lift : A → Lift j A

induction : {i j k : Level}
            {A : Type i} {P : Lift j A} →
            ((x : A) → P $ lift x) → ((x : Lift j A) → P x)
induction = ?
```
