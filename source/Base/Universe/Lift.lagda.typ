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
universe. Specifically, given a type $A ofType cal(U)_(i)$ a type universe
$cal(U)_(j)$, the type $Lift(A)$ is an
#link("note://367095ff-9cce-417f-a059-9c0290d0ca99")[inductive type] equipped
with a #link("note://367095ff-9cce-417f-a059-9c0290d0ca99")[constructor] $lift
ofType A -> Lift(A)_(cal(U)_(i union.sq j))$. The
#link("note://367095ff-9cce-417f-a059-9c0290d0ca99")[induction principle] for
$Lift(A)$ asserts that for any
#link("note://b05d0e2e-b6ab-45ab-9277-9559f4ee5e1f")[type family] $P$ indexed by
$x ofType Lift(A)$ there is a function
$
    induction_(Lift(A)) ofType piType(x, A) P(lift(x)) -> piType(x', Lift(A)_(cal(U)_(i union.sq j))) P(x')
$
such that the #link("note://367095ff-9cce-417f-a059-9c0290d0ca99")[computation
rule]
$
    induction_(Lift(A))(f, lift(x)) dot(eq) f(x).
$
holds for all $f ofType piType(x, A) P(lift(x))$ and $x ofType A$.


```agda
data Lift (j : Level) {i : Level} (A : Type i) : Type (i ⊔ j) where
  lift : A → Lift j A

induction : {i j k : Level}
            {A : Type i} {P : Lift j A → Type k} →
            ((x : A) → P $ lift x) → ((x : Lift j A) → P x)
induction p (lift x) = p x

recursion : {i j k : Level}
            {A : Type i} {B : Type k} →
            (A → B) → (Lift j A → B)
recursion = induction
```

= Universe lifting lower function <note:95201e7f-ee8c-474a-bc12-ad6dfcafa44a>
 
Let $A ofType cal(U)_(i)$ and let $cal(U)_j$ be a type universe. The `lower`
function sends elements of the
#link("note://b4f1235d-278b-497d-98f2-c215d1cd2cf4")[lifted] type
$Lift(A)_(cal(U)_(i union.sq j))$ to the corresponding elements in the
original type $A$.

```agda
lower : {i j : Level} {A : Type i} →
        Lift j A → A
lower (lift x) = x
```
