#import("../../../../../../library/template.typ"): *

#show: template

```agda
module Data.Sigma.Properties.Equivalence where

open import Base.Function.Core
open import Base.Function.Definitions
open import Base.Identity.Core
open import Base.Universe
open import Data.Sigma.Core
open import Data.Sigma.Definitions
```

= Product swap is its own inverse <note:3da4b91a-9d29-437d-aecd-794a120d4685>

#lemma(label: "9")[
    The #link("note://23a01b78-e433-4a66-8915-bfda82ee149a")[product]
    #link("note://ee77073e-2222-4957-9ed3-f8a120d8588d")[swap function] is its
    own #link("note://32c2ca55-63ba-411b-9052-676a51fd16a1")[inverse].
]
#proof[
    The #link("note://32c2ca55-63ba-411b-9052-676a51fd16a1")[relevant
    homotopies] hold #link("note://ee77073e-2222-4957-9ed3-f8a120d8588d")[by
    definition].
]

Note that I didn't say
#link("note://47767cc9-0064-45d3-8735-203b3236976d")[involutive]. The situation
is the same as #link("note://2311a766-22a2-4a85-91f2-1f3bc032cfff")[Lemma 7],
where I include a small explanation about this.

```agda
swapInverse :
  {i j : Level} {A : Type i} {B : Type j} →
  Inverse (swap {A = B} {B = A}) (swap {A = A} {B = B})
swapInverse = pair H H
  where
  H : {i j : Level} {A : Type i} {B : Type j} →
      (swap {A = B} {B = A}) ∘ (swap {A = A} {B = B}) ∼ identity
  H (pair x y) = reflexive
```

= Left and right product associate functions are inverses <note:52df8c7d-2587-4ddf-bfef-29de5ab739d1>

#lemma(label: "10")[
    The left and right
    #link("note://27424231-9e91-44a9-8311-360d17718901")[sigma associate
    functions] are
    #link("note://32c2ca55-63ba-411b-9052-676a51fd16a1")[inverses].
]
#proof[
    The #link("note://32c2ca55-63ba-411b-9052-676a51fd16a1")[relevant
    homotopies] hold #link("note://27424231-9e91-44a9-8311-360d17718901")[by
    definition].
]

```agda
Σ-associateInverse :
  {i j k : Level} {A : Type i} {B : A → Type j} {C : (x : A) → B x → Type k} →
  Inverse (associateˡ {A = A} {B = B} {C = C})
          (associateʳ {A = A} {B = B} {C = C})
Σ-associateInverse {A = A} {B = B} {C = C} = pair H K
  where
  H : associateʳ ∘ associateˡ ∼ (identity {_} {Σ (Σ A B) (uncurry C)})
  H (pair (pair x y) z) = reflexive

  K : associateˡ ∘ associateʳ ∼ (identity {_} {Σ A (λ x → Σ (B x) (C x))})
  K (pair x (pair y z)) = reflexive

×-associateInverse :
  {i j k : Level} {A : Type i} {B : Type j} {C : Type k} →
  Inverse (associateˡ' {A = A} {B = B} {C = C})
          (associateʳ' {A = A} {B = B} {C = C})
×-associateInverse {A = A} {B = B} {C = C} = pair H K
  where
  H : associateʳ' ∘ associateˡ' ∼ (identity {_} {(A × B) × C})
  H (pair (pair x y) z) = reflexive

  K : associateˡ' ∘ associateʳ' ∼ (identity {_} {A × (B × C)})
  K (pair x (pair y z)) = reflexive
```
