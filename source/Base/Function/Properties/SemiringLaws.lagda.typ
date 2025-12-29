#import("../../../../../../library/template.typ"): *

#show: template

```agda
module Base.Function.Properties.SemiringLaws where

open import Base.Function.Core
open import Base.Function.Definitions
open import Base.Function.Negation
open import Base.Function.Properties.Equivalence
open import Base.Identity.Core
open import Base.Universe.Core
open import Data.Coproduct.Core
open import Data.Coproduct.Definitions as Coproduct
open import Data.Coproduct.Properties.Equivalence as Coproduct
open import Data.Empty as Empty
open import Data.Sigma.Core
open import Data.Sigma.Definitions as Sigma
open import Data.Sigma.Properties.Equivalence as Sigma
open import Data.Unit.Core
```

= Coproducts satisfy the unit laws up to equivalence with respect to the empty type <note:f5ac35b4-ac3e-4b2c-984e-28edc4e7c935>

#lemma(supplement: cite_link(<rijke2025>, "Rijke 2025, ex. 9.2.9"))[
    For every type $A$, there are
    #link("note://32c2ca55-63ba-411b-9052-676a51fd16a1")[equivalences]
    $
        0 + A tilde.eq A quad "and" quad A + 0 tilde.eq A.
    $
]
#proof[
    By #link("note://b7b0a00f-26af-486c-b13d-6f5160fbb2d0")[Lemma 6], the maps
    $resolve2 ofType 0 + A -> A$ and $resolve1 ofType A + 0 -> A$ (see
    #link("note://4af48c11-22e0-4aae-89eb-fad6d4320836")[Negation resolution])
    have #link("note://32c2ca55-63ba-411b-9052-676a51fd16a1")[inverses] (namely
    $inject2$ and $inject1$). It follows by
    #link("note://731be08a-a2ad-477a-8c08-d9f26c32de41")[Lemma 3] that
    $resolve2$ and $resolve1$ are equivalences.
]

See #link("note://001d31c7-7fb6-4878-883a-ff464bb9c0a8")[Coproduct type] and
#link("note://9d7cf197-7f2a-4633-aa63-1c9df1429a13")[Empty type].

```agda
＋-unitˡ : {i : Level} (A : Type i) →
           (𝟎 ＋ A) ≃ A
＋-unitˡ A =
  inverse→≃ (resolve₂ Empty.recursion)
            inject₂
            (resolve₂-inject₂-inverse Empty.recursion)

＋-unitʳ : {i : Level} (A : Type i) →
           (A ＋ 𝟎) ≃ A
＋-unitʳ A =
  inverse→≃ (resolve₁ Empty.recursion)
            inject₁
            (resolve₁-inject₁-inverse Empty.recursion)
```

= Coproducts are commutative up to equivalence <note:f7e09aa1-5bd3-40e4-824e-f242b481967c>

#link("note://001d31c7-7fb6-4878-883a-ff464bb9c0a8")[Coproducts] are
#link("note://22261946-d41d-4db3-849d-0511c26b0dea")[commutative] up to
#link("note://32c2ca55-63ba-411b-9052-676a51fd16a1")[equivalence].
 
#lemma(supplement: cite_link(<rijke2025>, "Rijke 2025, ex. 9.2.9"))[
    For all types $A$ and $B$, there is an
    #link("note://32c2ca55-63ba-411b-9052-676a51fd16a1")[equivalence] $A + B
    tilde.eq B + A$.
]

#proof[
    By #link("note://2311a766-22a2-4a85-91f2-1f3bc032cfff")[Lemma 7].
]

```agda
＋-commutative : {i j : Level} (A : Type i) (B : Type j) →
                (A ＋ B) ≃ (B ＋ A)
＋-commutative A B =
  inverse→≃ Coproduct.swap Coproduct.swap Coproduct.swapInverse
```

= Coproducts are associative up to equivalence <note:30a3f3af-3df3-4622-817d-16e85e2172d8>

#link("note://001d31c7-7fb6-4878-883a-ff464bb9c0a8")[Coproducts] are
#link("note://9affcc46-5cf0-4627-b909-80ec3cba8a2d")[associative] up to
#link("note://32c2ca55-63ba-411b-9052-676a51fd16a1")[equivalence].
 
#lemma(supplement: cite_link(<rijke2025>, "Rijke 2025, ex. 9.2.9"))[
    For all types $A$ and $B$, there is an
    #link("note://32c2ca55-63ba-411b-9052-676a51fd16a1")[equivalence]
    $
        (A + B) + C tilde.eq A + (B + C).
    $
]
#proof[
    By #link("note://9ef10dfd-e951-4cad-a7cb-beae239f4f2c")[Lemma 8].
]

```agda
＋-associative : {i j k : Level}
                (A : Type i) (B : Type j) (C : Type k) →
                ((A ＋ B) ＋ C) ≃ (A ＋ (B ＋ C))
＋-associative A B C =
  inverse→≃ Coproduct.associateˡ Coproduct.associateʳ Coproduct.associateInverse
```

= Products are annihilative up to equivalence with respect to the empty type <note:76a8dcb0-3cbb-4ae2-80cc-df7800fef2c4>
 
#link("note://23a01b78-e433-4a66-8915-bfda82ee149a")[Products] are annihilative
up to #link("note://32c2ca55-63ba-411b-9052-676a51fd16a1")[equivalence].

#lemma(supplement: cite_link(<rijke2025>, "Rijke 2025, ex. 9.2.9"))[
    For every type $A$, there are
    #link("note://32c2ca55-63ba-411b-9052-676a51fd16a1")[equivalences]
    $
        (emptyType times A) & tilde.eq emptyType, \
        (A times emptyType) & tilde.eq emptyType.
    $
]
#proof[
    Use the #link("note://9d7cf197-7f2a-4633-aa63-1c9df1429a13")[recursion
    principle for the empty type].
]

```agda
×-annihilativeˡ : {i : Level} (A : Type i) →
                  (𝟎 × A) ≃ 𝟎
×-annihilativeˡ A = inverse→≃ project₁ Empty.recursion (pair H K) 
  where
  H : Empty.recursion ∘ project₁ ∼ (identity {_} {𝟎 × A})
  H (pair z x) = Empty.recursion z

  K : project₁ ∘ Empty.recursion ∼ (identity {_} {𝟎})
  K ()

×-annihilativeʳ : {i : Level} (A : Type i) →
                  (A × 𝟎) ≃ 𝟎
×-annihilativeʳ A = inverse→≃ project₂ Empty.recursion (pair H K)
  where
  H : Empty.induction ∘ project₂ ∼ (identity {_} {A × 𝟎})
  H (pair x z) = Empty.recursion z

  K : project₂ ∘ Empty.recursion ∼ (identity {_} {𝟎})
  K ()
```

= Products satisfy the unit laws up to equivalence with respect to the unit type <note:0e31cc9f-c207-459c-9208-1453d91c976f>
 
#link("note://23a01b78-e433-4a66-8915-bfda82ee149a")[Products] satisfy the unit
laws up to #link("note://32c2ca55-63ba-411b-9052-676a51fd16a1")[equivalence]
with respect to the #link("note://fe0ba530-46e9-4031-83bb-330db4d12b4e")[unit
type].

#lemma(supplement: cite_link(<rijke2025>, "Rijke 2025, ex. 9.2.9"))[
    For every type $A$, there are
    #link("note://32c2ca55-63ba-411b-9052-676a51fd16a1")[equivalences]
    $
        (unitType times A) tilde.eq A quad "and" quad
        (A times unitType) tilde.eq A.
    $
]
#proof[
    The #link("note://32c2ca55-63ba-411b-9052-676a51fd16a1")[relevant
    homotopies] hold by definition (See
    #link("note://fe0ba530-46e9-4031-83bb-330db4d12b4e")[Unit type] and
    #link("note://23a01b78-e433-4a66-8915-bfda82ee149a")[Product type]).
]

```agda
×-unitˡ : {i : Level} → (A : Type i) → (𝟏 × A) ≃ A
×-unitˡ A = inverse→≃ project₂ (pair {B = constant A} ⋆) (pair H K) 
  where
  H : (pair ⋆) ∘ project₂ ∼ (identity {_} {𝟏 × A})
  H (pair ⋆ x) = reflexive

  K : (project₂ {A = 𝟏} {B = constant A}) ∘ (pair ⋆) ∼ (identity {_} {A})
  K x = reflexive

×-unitʳ : {i : Level} → (A : Type i) → (A × 𝟏) ≃ A
×-unitʳ A = inverse→≃ project₁ (flip pair ⋆) (pair H K)
  where
  H : (flip pair ⋆) ∘ project₁ ∼ (identity {_} {A × 𝟏})
  H (pair x ⋆) = reflexive

  K : project₁ ∘ (flip pair ⋆) ∼ (identity {_} {A})
  K x = reflexive
```

= Products are commutative up to equivalence <note:9327c53c-1b28-4d36-89cf-d7d51a91d705>

#link("note://23a01b78-e433-4a66-8915-bfda82ee149a")[Products] are
#link("note://22261946-d41d-4db3-849d-0511c26b0dea")[commutative] up to
#link("note://32c2ca55-63ba-411b-9052-676a51fd16a1")[equivalence].

#lemma(
    label: "53",
    supplement: cite_link(<rijke2025>, "Rijke 2025, ex. 9.2.9")
)[
    For all types $A$ and $B$, there is an
    #link("note://32c2ca55-63ba-411b-9052-676a51fd16a1")[equivalence]
    $
        A times B tilde.eq B times A.
    $
]
#proof[
    By #link("note://3da4b91a-9d29-437d-aecd-794a120d4685")[Lemma 9].
]

```agda
×-commutative : {i j : Level} (A : Type i) (B : Type j) →
                (A × B) ≃ (B × A)
×-commutative A B = inverse→≃ Sigma.swap Sigma.swap Sigma.swapInverse
```

= Products are associative up to equivalence <note:771c86cd-ddcf-4bc7-aa95-b1482c2d34d1>

#link("note://23a01b78-e433-4a66-8915-bfda82ee149a")[Products] are
#link("note://9affcc46-5cf0-4627-b909-80ec3cba8a2d")[associative] up to
#link("note://32c2ca55-63ba-411b-9052-676a51fd16a1")[equivalence].

#lemma(supplement: cite_link(<rijke2025>, "Rijke 2025, ex. 9.2.9"))[
    For all types $A$, $B$, and $C$, there is an
    #link("note://32c2ca55-63ba-411b-9052-676a51fd16a1")[equivalence]
    $
        (A times B) times C tilde.eq A times (B times C).
    $
]
#proof[
    By #link("note://52df8c7d-2587-4ddf-bfef-29de5ab739d1")[Lemma 10].
]

```agda
×-associative : {i j k : Level}
                (A : Type i) (B : Type j) (C : Type k) →
                ((A × B) × C) ≃ (A × (B × C))
×-associative A B C =
  inverse→≃ Sigma.associateˡ'
            Sigma.associateʳ'
            Sigma.×-associateInverse
```

= Products distribute over coproducts up to equivalence <note:9c6f7ba6-5511-4fc4-a2c4-33808625b2fc>

#link("note://23a01b78-e433-4a66-8915-bfda82ee149a")[Products]
#link("note://950bc0dc-2afc-4bd1-beab-ad2895783cc5")[distribute over]
#link("note://001d31c7-7fb6-4878-883a-ff464bb9c0a8")[coproducts] up to
#link("note://32c2ca55-63ba-411b-9052-676a51fd16a1")[equivalence].
 
#lemma(supplement: cite_link(<rijke2025>, "ex. 9.2.9"))[
    For all types $A$, $B$, and $C$, there is are
    #link("note://32c2ca55-63ba-411b-9052-676a51fd16a1")[equivalences]
    $
        A times (B + C) & tilde.eq (A times B) + (A times C), \
        (A + B) times C) & tilde.eq (A times C) + (A times C).
    $
]
#proof[
    Use the natural maps back and forth. The
    #link("note://32c2ca55-63ba-411b-9052-676a51fd16a1")[relevant homotopies]
    hold by definition.
]

```agda
×-distributesOverˡ-＋ :
  {i j k : Level} →
  (A : Type i) (B : Type j) (C : Type k) →
  A × (B ＋ C) ≃ (A × B ＋ A × C)
×-distributesOverˡ-＋ A B C = inverse→≃ f g (pair H K)
  where
  f : A × (B ＋ C) → (A × B ＋ A × C)
  f (pair x (inject₁ y)) = inject₁ (pair x y)
  f (pair x (inject₂ z)) = inject₂ (pair x z)

  g : (A × B ＋ A × C) → A × (B ＋ C)
  g (inject₁ (pair x y)) = pair x (inject₁ y)
  g (inject₂ (pair x z)) = pair x (inject₂ z)

  H : g ∘ f ∼ identity
  H (pair x (inject₁ y)) = reflexive
  H (pair x (inject₂ z)) = reflexive

  K : f ∘ g ∼ identity
  K (inject₁ (pair x y)) = reflexive
  K (inject₂ (pair x z)) = reflexive

×-distributesOverʳ-＋ :
  {i j k : Level}
  (A : Type i) (B : Type j) (C : Type k) →
  (A ＋ B) × C ≃ (A × C ＋ B × C)
×-distributesOverʳ-＋ A B C = inverse→≃ f g (pair H K)
  where
  f : (A ＋ B) × C → (A × C ＋ B × C)
  f (pair (inject₁ x) z) = inject₁ (pair x z)
  f (pair (inject₂ y) z) = inject₂ (pair y z)

  g : (A × C ＋ B × C) → (A ＋ B) × C
  g (inject₁ (pair x z)) = pair (inject₁ x) z
  g (inject₂ (pair y z)) = pair (inject₂ y) z

  H : g ∘ f ∼ identity
  H (pair (inject₁ x) z) = reflexive
  H (pair (inject₂ y) z) = reflexive

  K : f ∘ g ∼ identity
  K (inject₁ (pair x z)) = reflexive
  K (inject₂ (pair y z)) = reflexive
```

= Sigma types are annihilative up to equivalence with respect to the empty type <note:04566554-5ac9-4f1f-85b9-50256d1fe220>

The #link("note://ae098784-7572-4d29-b548-a2db9b6d004a")[$Sigma$-type] is
annihilative up to
#link("note://32c2ca55-63ba-411b-9052-676a51fd16a1")[equivalence] with respect
to the #link("note://9d7cf197-7f2a-4633-aa63-1c9df1429a13")[empty type].
 
#lemma(supplement: cite_link(<rijke2025>, "Rijke 2025, ex. 9.2.10"))[
    For any #link("note://b05d0e2e-b6ab-45ab-9277-9559f4ee5e1f")[type family]
    $B$ over $emptyType$, there is an
    #link("note://32c2ca55-63ba-411b-9052-676a51fd16a1")[equivalence]
    $
        sigmaType(x, emptyType) B(x) tilde.eq emptyType.
    $
    Similarly, for any type $A$, there is an equivalence
    $
        sigmaType(x, A) emptyType tilde.eq emptyType.
    $
]
#proof[
    Use the recursion principle for the
    #link("note://9d7cf197-7f2a-4633-aa63-1c9df1429a13")[empty type].
]

```agda
Σ-annihilativeˡ : {i : Level} (B : 𝟎 → Type i) →
                  (Σ 𝟎 B) ≃ 𝟎
Σ-annihilativeˡ B = inverse→≃ project₁ Empty.recursion (pair H K)
  where
  H : Empty.recursion ∘ project₁ ∼ identity {_} {Σ 𝟎 B}
  H (pair x y) = Empty.recursion x

  K : project₁ ∘ Empty.recursion ∼ identity {_} {𝟎}
  K ()

Σ-annihilativeʳ : {i : Level} (A : Type i) →
                  (Σ A (constant 𝟎)) ≃ 𝟎
Σ-annihilativeʳ A = inverse→≃ project₂ Empty.recursion (pair H K)
  where
  H : Empty.recursion ∘ project₂ ∼ identity {_} {Σ A (constant 𝟎)}
  H (pair x y) = Empty.recursion y

  K : project₂ ∘ Empty.recursion ∼ identity {_} {𝟎}
  K ()
```

= Sigma types satisfy the unit laws up to equivalence with respect to the unit type <note:95454f1f-3586-4c87-b04f-3e3d1dbb2598>

The #link("note://ae098784-7572-4d29-b548-a2db9b6d004a")[$Sigma$-type] satisfies
the unit laws up to
#link("note://32c2ca55-63ba-411b-9052-676a51fd16a1")[equivalence] with respect
to the #link("note://fe0ba530-46e9-4031-83bb-330db4d12b4e")[unit type].

#lemma(supplement: cite_link(<rijke2025>, "Rijke 2025, ex. 9.2.10"))[
    For any type family $B$ over $unitType$, there is an
    #link("note://32c2ca55-63ba-411b-9052-676a51fd16a1")[equivalence]
    $
        sigmaType(x, unitType) B(x) tilde.eq B(star).
    $
    Similarly, for any type $A$, there is an equivalence
    $
        sigmaType(x, A) unitType tilde.eq A.
    $
]
#proof[
    Use the natural maps back and forth. The
    #link("note://32c2ca55-63ba-411b-9052-676a51fd16a1")[required homotopies]
    hold by definition.
]

```agda
Σ-unitˡ : {i : Level} (B : 𝟏 → Type i) →
          (Σ 𝟏 B) ≃ (B ⋆)
Σ-unitˡ B = inverse→≃ f (pair ⋆) (pair H K)
  where
  f : Σ 𝟏 B → B ⋆
  f (pair ⋆ y) = y

  H : (pair ⋆) ∘ f ∼ (identity {_} {Σ 𝟏 B})
  H (pair ⋆ y) = reflexive

  K : f ∘ (pair ⋆) ∼ (identity {_} {B ⋆})
  K x = reflexive

Σ-unitʳ : {i : Level} (A : Type i) →
          (Σ A (constant 𝟏)) ≃ A
Σ-unitʳ A = inverse→≃ project₁ (flip pair ⋆) (pair H K)
  where
  H : (flip pair ⋆) ∘ project₁ ∼ (identity {_} {Σ A (constant 𝟏)})
  H (pair x ⋆) = reflexive

  K : project₁ ∘ (flip pair ⋆) ∼ (identity {_} {A})
  K x = reflexive
```

= Sigma types are associative up to equivalence <note:ccf17e09-7e2d-4a7c-91f7-0a5d5b4f4b31>

The #link("note://ae098784-7572-4d29-b548-a2db9b6d004a")[$Sigma$-type] is
#link("note://9affcc46-5cf0-4627-b909-80ec3cba8a2d")[associative] up to
#link("note://32c2ca55-63ba-411b-9052-676a51fd16a1")[equivalence].

#lemma(supplement: cite_link(<rijke2025>, "Rijke 2025, ex. 9.2.10"))[
    Let $B$ be a #link("note://b05d0e2e-b6ab-45ab-9277-9559f4ee5e1f")[type
    family] over a type $A$. If $C(x, y)$ is a type family indexed by $x ofType
    A$ and $y ofType B(x)$, then there is an
    #link("note://32c2ca55-63ba-411b-9052-676a51fd16a1")[equivalence]
    $
        sigmaType(u, sigmaType(x, A) B(x)) C(project1(u), project2(u)) tilde.eq
        sigmaType(x, A) sigmaType(y, B(x)) C(x, y).
    $

    Similarly, if $C(u)$ is a type family indexed by $u ofType sigmaType(x, A)
    B(x)$, then there is an equivalence
    $
        sigmaType(u, sigmaType(x, A) B(x)) C(u) tilde.eq
        sigmaType(x, A) sigmaType(y, B(x)) C(pair(x, y)).
    $
]
#proof[
    By #link("note://52df8c7d-2587-4ddf-bfef-29de5ab739d1")[Lemma 10].
]

```agda
Σ-associative :
  {i j k : Level}
  (A : Type i) (B : A → Type j) (C : (x : A) → B x → Type k) →
  (Σ (Σ A B) (uncurry C)) ≃ (Σ A (λ x → Σ (B x) (C x)))
Σ-associative A B C =
  inverse→≃ Sigma.associateˡ
            Sigma.associateʳ
            Sigma.Σ-associateInverse

Σ-associativeCurried :
  {i j k : Level}
  (A : Type i) (B : A → Type j) (C : (Σ A B) → Type k) →
  (Σ (Σ A B) C) ≃ (Σ A (λ x → Σ (B x) (curry C x)))
Σ-associativeCurried A B C =
  inverse→≃ Sigma.associateCurriedˡ
            Sigma.associateCurriedʳ
            Sigma.Σ-associateCurriedInverse
```

= Sigma types distribute over coproducts up to equivalence <note:53dc7355-99c1-4b15-a9b3-dbe0023a02e6>

The #link("note://ae098784-7572-4d29-b548-a2db9b6d004a")[$Sigma$-type]
#link("note://950bc0dc-2afc-4bd1-beab-ad2895783cc5")[distributes over]
#link("note://001d31c7-7fb6-4878-883a-ff464bb9c0a8")[coproducts] up to
#link("note://32c2ca55-63ba-411b-9052-676a51fd16a1")[equivalence].
 
#lemma(supplement: cite_link(<rijke2025>, "Rijke 2025, ex. 9.2.10"))[
    Let $B$ be a #link("note://b05d0e2e-b6ab-45ab-9277-9559f4ee5e1f")[type
    family] over a type $A$. If $C(x)$ is a type family indexed by $x ofType A$,
    then there is an
    #link("note://32c2ca55-63ba-411b-9052-676a51fd16a1")[equivalence]
    $
        sigmaType(x, A) B(x) + C(x) tilde.eq
        (sigmaType(x, A) B(x)) + (sigmaType(x, A) C(x)).
    $
    Similarly, if $C(u)$ is a family indexed by $u ofType A + B$, then there is
    an equivalence
    $
        sigmaType(u, A + B) C(u) tilde.eq
        (sigmaType(x, A) C(inject1(x))) + (sigmaType(y, B) C(inject2(y))).
    $
]
#proof[
    Take the natural maps back and forth. The
    #link("note://32c2ca55-63ba-411b-9052-676a51fd16a1")[required homotopies]
    hold by definition.
]

```agda
Σ-distributesOverˡ-＋ :
  {i j k : Level}
  (A : Type i) (B : A → Type j) (C : A → Type k) →
  (Σ A (λ x → B x ＋ C x)) ≃ ((Σ A B) ＋ (Σ A C))
Σ-distributesOverˡ-＋ A B C = inverse→≃ f g (pair H K)
  where
  f : (Σ A (λ x → B x ＋ C x)) → ((Σ A B) ＋ (Σ A C))
  f (pair x (inject₁ y)) = inject₁ (pair x y)
  f (pair x (inject₂ z)) = inject₂ (pair x z)

  g : ((Σ A B) ＋ (Σ A C)) → (Σ A (λ x → B x ＋ C x))
  g (inject₁ (pair x y)) = pair x (inject₁ y)
  g (inject₂ (pair x z)) = pair x (inject₂ z)

  H : g ∘ f ∼ (identity {_} {Σ A (λ x → B x ＋ C x)})
  H (pair x (inject₁ y)) = reflexive
  H (pair x (inject₂ z)) = reflexive

  K : f ∘ g ∼ (identity {_} {Σ A B ＋ Σ A C})
  K (inject₁ (pair x y)) = reflexive
  K (inject₂ (pair x z)) = reflexive


Σ-distributesOverʳ-＋ :
  {i j k : Level}
  (A : Type i) (B : Type j) (C : (A ＋ B) → Type k) →
  (Σ (A ＋ B) C) ≃ ((Σ A (C ∘ inject₁)) ＋ (Σ B (C ∘ inject₂)))
Σ-distributesOverʳ-＋ A B C = inverse→≃ f g (pair H K)
  where
  f : (Σ (A ＋ B) C) → ((Σ A (C ∘ inject₁)) ＋ (Σ B (C ∘ inject₂)))
  f (pair (inject₁ x) z) = inject₁ (pair x z)
  f (pair (inject₂ y) z) = inject₂ (pair y z)

  g : ((Σ A (C ∘ inject₁)) ＋ (Σ B (C ∘ inject₂))) → (Σ (A ＋ B) C)
  g (inject₁ (pair x z)) = pair (inject₁ x) z
  g (inject₂ (pair y z)) = pair (inject₂ y) z

  H : g ∘ f ∼ (identity {_} {Σ (A ＋ B) C})
  H (pair (inject₁ x) z) = reflexive
  H (pair (inject₂ y) z) = reflexive

  K : f ∘ g ∼ (identity {_} {Σ A (C ∘ inject₁) ＋ Σ B (C ∘ inject₂)})
  K (inject₁ (pair x z)) = reflexive
  K (inject₂ (pair y z)) = reflexive
```
