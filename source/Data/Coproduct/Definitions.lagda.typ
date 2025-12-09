#import("../../../../../library/template.typ"): *

#show: template

```agda
module Data.Coproduct.Definitions where

open import Base.Function.Core
open import Base.Universe
open import Data.Coproduct.Core
```

= Coproduct map <note:95fefab8-ba33-4759-8a33-03997164ebab>
 
Given maps $f ofType A -> C$, $g ofType B -> D$, we can define a map on
#link("note://001d31c7-7fb6-4878-883a-ff464bb9c0a8")[coproducts] $f + g ofType A
+ B -> C + D$ by

$
    (f + g)(inject1(x)) & := inject1(f(x)), \
    (f + g)(inject2(y)) & := inject2(g(y)).
$

```agda
map : {i j i' j' : Level}
      {A : Type i} {B : Type j} {C : Type i'} {D : Type j'} →
      (A → C) → (B → D) → (A ＋ B → C ＋ D)
map f g = recursion (inject₁ ∘ f) (inject₂ ∘ g)
```

We also define special cases which only modify one side or the other.

```agda
map₁ : {i j k : Level} {A : Type i} {B : Type j} {C : Type k} →
       (A → C) → (A ＋ B → C ＋ B)
map₁ = flip map identity

map₂ : {i j k : Level} {A : Type i} {B : Type j} {C : Type k} →
       (B → C) → (A ＋ B → A ＋ C) 
map₂ = map identity
```
