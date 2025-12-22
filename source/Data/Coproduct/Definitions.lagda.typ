#import("../../../../../library/template.typ"): *

#show: template

```agda
module Data.Coproduct.Definitions where

open import Base.Function.Core
open import Base.Universe.Core
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

= Coproduct swap <note:9ca63218-a429-4ee5-966c-89b4eb0c484f>

We define a #link("note://001d31c7-7fb6-4878-883a-ff464bb9c0a8")[coproduct] swap
function $A + B -> B + A$. This is used in the proof that
#link("note://f7e09aa1-5bd3-40e4-824e-f242b481967c")[coproducts are commutative
up to equivalence].

```agda
swap : {i j : Level} {A : Type i} {B : Type j} →
       A ＋ B → B ＋ A
swap (inject₁ x) = inject₂ x
swap (inject₂ y) = inject₁ y
```

= Coproduct associate <note:70f0207b-40b0-4f50-9184-f0226ae0d956>
 
We define #link("note://001d31c7-7fb6-4878-883a-ff464bb9c0a8")[coproduct]
#link("note://9affcc46-5cf0-4627-b909-80ec3cba8a2d")[associate] maps $(A + B) +
C -> A + (B + C)$ and $A + (B + C) -> (A + B) + C$. These are used in the proof
that #link("note://30a3f3af-3df3-4622-817d-16e85e2172d8")[coproducts are
associative up to equivalence].

```agda
associateˡ : {i j k : Level} {A : Type i} {B : Type j} {C : Type k} →
             (A ＋ B) ＋ C → A ＋ (B ＋ C)
associateˡ (inject₁ (inject₁ x)) = inject₁ x
associateˡ (inject₁ (inject₂ y)) = inject₂ (inject₁ y)
associateˡ (inject₂ z) = inject₂ (inject₂ z)

associateʳ : {i j k : Level} {A : Type i} {B : Type j} {C : Type k} →
             A ＋ (B ＋ C) → (A ＋ B) ＋ C
associateʳ (inject₁ x) = inject₁ (inject₁ x)
associateʳ (inject₂ (inject₁ x)) = inject₁ (inject₂ x)
associateʳ (inject₂ (inject₂ x)) = inject₂ x
```
