#import("../../../../../../library/template.typ"): *

#show: template

```agda
module Data.Sigma.Properties.Equivalence where

open import Base.Function.Core
open import Base.Function.Definitions
open import Base.Function.Properties.Equivalence
open import Base.Identity.Core
open import Base.Universe.Core
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

swapIsEquivalence :
  {i j : Level} {A : Type i} {B : Type j} →
  IsEquivalence (swap {A = A} {B = B})
swapIsEquivalence = inverse→isEquivalence swap swap swapInverse
```

= Left and right sigma associate functions are inverses <note:52df8c7d-2587-4ddf-bfef-29de5ab739d1>

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

Σ-associateCurriedInverse :
  {i j k : Level}
  {A : Type i} {B : A → Type j} {C : (Σ A B) → Type k} →
  Inverse (associateCurriedˡ {A = A} {B = B} {C = C})
          (associateCurriedʳ {A = A} {B = B} {C = C})
Σ-associateCurriedInverse {A = A} {B = B} {C = C} = pair H K
  where
  H : associateCurriedʳ ∘ associateCurriedˡ ∼ (identity {_} {Σ (Σ A B) C})
  H (pair (pair x y) z) = reflexive

  K : associateCurriedˡ ∘ associateCurriedʳ ∼
      (identity {_} {Σ A (λ x → Σ (B x) (curry C x))})
  K (pair x (pair y z)) = reflexive
```

= Double sigma base swap equivalence on right <note:0e627eaa-64e9-47a5-b5a3-37a4e92ba151>
 
#lemma(supplement: cite_link(<rijke2025>, "Rijke 2025, exer. 9.5(a)"))[
    Let $A$ and $B$ be types, and let $C(x, y)$ be a
    #link("note://b05d0e2e-b6ab-45ab-9277-9559f4ee5e1f")[type family] indexed by
    $x ofType A$ and $y ofType B$. Then there is an
    #link("note://32c2ca55-63ba-411b-9052-676a51fd16a1")[equivalence]
    $
        sigmaType(x, A) sigmaType(y, B) C(x, y) tilde.eq
        sigmaType(y, B) sigmaType(x, A) C(x, y)
    $
]
#proof[
    Use #link("note://ae098784-7572-4d29-b548-a2db9b6d004a")[$Sigma$-recursion]
    to define the natural maps back and forth. The
    #link("note://32c2ca55-63ba-411b-9052-676a51fd16a1")[required homotopies]
    then hold by definition.
]

```agda
swapBaseʳ-inverse :
  {i j k : Level} {A : Type i} {B : Type j} {C : A → B → Type k} →            
  Inverse (swapBaseʳ {A = A} {B = B} {C = C})
          (swapBaseʳ {A = B} {B = A} {C = flip C})
swapBaseʳ-inverse {A = A} {B = B} {C = C} = pair H H
  where
  H : {i j k : Level} {A : Type i} {B : Type j} {C : A → B → Type k} →            
      swapBaseʳ ∘ swapBaseʳ ∼ identity {_} {Σ A (λ x → Σ B (λ y → C x y))}
  H (pair x (pair y z)) = reflexive

swapBaseʳ-≃ : 
  {i j k : Level} {A : Type i} {B : Type j} {C : A → B → Type k} →            
  Σ A (λ x → Σ B (λ y → C x y)) ≃ Σ B (λ y → Σ A (λ x → C x y))
swapBaseʳ-≃ = inverse→≃ swapBaseʳ swapBaseʳ swapBaseʳ-inverse
```

= Double sigma base swap equivalence on left <note:8654b3c4-caef-412d-aef6-3e31dcc2418b>
 
#lemma(supplement: cite_link(<rijke2025>, "Rijke 2025, exer. 9.5(b)"))[
    Let $B$ and $C$ be #link("note://b05d0e2e-b6ab-45ab-9277-9559f4ee5e1f")[type
    families] over a type $A$. There is an
    #link("note://32c2ca55-63ba-411b-9052-676a51fd16a1")[equivalence]
    $
        sigmaType(u, sigmaType(x, A) B(x)) C(project1(u)) tilde.eq
        sigmaType(v, sigmaType(x, A) C(x)) B(project1(v)).
    $
]
#proof[
    Use the #link("note://2b484b41-4405-42e7-bd4d-e35dbe878770")[natural maps
    back and forth]. The
    #link("note://32c2ca55-63ba-411b-9052-676a51fd16a1")[required homotopies]
    then hold by definition.
]

```agda
swapBaseˡ-inverse : 
  {i j k : Level} {A : Type i} {B : A → Type j} {C : A → Type k} →            
  Inverse (swapBaseˡ {A = A} {B = B} {C = C})
          (swapBaseˡ {A = A} {B = C} {C = B})
swapBaseˡ-inverse = pair H H
  where
  H : {i j k : Level} {A : Type i} {B : A → Type j} {C : A → Type k} →            
      swapBaseˡ {B = C} {C = B} ∘ swapBaseˡ ∼
      (identity {_} {Σ (Σ A B) (C ∘ project₁)})
  H (pair (pair x y) z) = reflexive
```
