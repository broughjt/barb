#import("../../../../../library/template.typ"): *

#show: template

```agda
module Data.Sigma.Definitions where

open import Base.Function.Core
open import Base.Universe
open import Data.Sigma.Core
```

= Currying and uncurring <note:bc0fb217-3c37-4034-9681-ab3040569951>
 
In functional programming, *currying* transforms a function taking multiple
arguments in the form of a
#link("note://ae098784-7572-4d29-b548-a2db9b6d004a")[product] into a sequence of
higher order functions, each of a single argument.

If we have a function $f ofType A times B -> C$, the curried form of this
function would be $f' ofType A -> (B -> C)$, where the application of $f'$ to
each $x ofType A$ yields a new function $f'(x) ofType B -> C$.

We can define a *curry* operator as a higher-order function which takes a
function on #link("note://ae098784-7572-4d29-b548-a2db9b6d004a")[pairs] and
returns its curried form. We allow
#link("note://ae098784-7572-4d29-b548-a2db9b6d004a")[dependent products], not
just ordinary #link("note://23a01b78-e433-4a66-8915-bfda82ee149a")[Cartesian
products] as in the example above.

```agda
curry : {i j k : Level} {A : Type i} {B : A → Type j} {C : Σ A B → Type k} →
        ((u : Σ A B) → C u) →
        ((x : A) → (y : B x) → C $ pair x y)
curry f x y = f $ pair x y
```

We can also define an *uncurry* operator, which takes a curried function and
returns a verion which takes its argument as a pair.

```agda
uncurry : {i j k : Level}
          {A : Type i} {B : A → Type j} {C : (x : A) → B x → Type k} →
          ((x : A) (y : B x) → C x y) →
          ((u : Σ A B) → C (project₁ u) (project₂ u))
uncurry {C = C} = induction {P = λ u → C (project₁ u) (project₂ u)}
```

Compare #cite(<rijke2025>, form: "prose", supplement: "rem. 4.6.3").
