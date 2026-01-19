#import("../../../../../../library/template.typ"): *

#show: template

```agda
module Data.Coproduct.Properties.Equivalence where

open import Base.Function.Core
open import Base.Function.Definitions
open import Base.Function.Negation
open import Base.Function.Properties.Equivalence
open import Base.Identity.Core
open import Base.Universe.Core
open import Data.Coproduct.Core
open import Data.Coproduct.Definitions as Coproduct
open import Data.Coproduct.Properties.Identity
open import Data.Sigma.Core
```

= Negation resolution and injections are inverses <note:b7b0a00f-26af-486c-b13d-6f5160fbb2d0>

#lemma(label: "6")[
    Consider types $A$ and $B$. If $f ofType not B$. then the functions
    $resolve1(f) ofType A + B -> A$ (constructed in
    #link("note://4af48c11-22e0-4aae-89eb-fad6d4320836")[Lemma 5]) and $inject1
    ofType A -> A + B$ are
    #link("note://32c2ca55-63ba-411b-9052-676a51fd16a1")[inverses]. Similarly,
    if $g ofType not A$, then $resolve2(g) ofType A + B -> B$ and $inject2
    ofType B -> A + B$ are inverses.
]
#proof[
    Use #link("note://5e5e6ae4-329b-473f-b13c-c2cbd77534b6")[proof of negation
    by absurdity] when handling the case for the
    #link("note://16ffba35-7712-4eb7-8902-0812e529aa16")[negated] type. The
    other #link("note://3cb1b8ca-2a77-4c8a-b726-ed8f10dfd208")[homotopies]
    follow by definition (see
    #link("note://4af48c11-22e0-4aae-89eb-fad6d4320836")[Negation resolution]
    and #link("note://001d31c7-7fb6-4878-883a-ff464bb9c0a8")[Coproduct type]).
]

See #link("note://6aa2ace5-0120-4fb0-9681-1db6875a84c5")[Lemma 69], which shows
the #link("note://314a5e4f-bf3c-497a-867c-edc5bb306d7f")[converse] statement.

```agda
resolve₁-inject₁-inverse :
  {i j : Level} {A : Type i} {B : Type j}
  (f : ¬ B) →
  Inverse (resolve₁ {A = A} {B = B} f) inject₁
resolve₁-inject₁-inverse {A = A} {B = B} f = pair H K
  where
  H : inject₁ ∘ resolve₁ f ∼ identity {_} {A ＋ B}
  H (inject₁ x) = reflexive
  H (inject₂ y) = absurd y f

  K : RightInverse (resolve₁ f) inject₁
  K x = reflexive

resolve₂-inject₂-inverse :
  {i j : Level} {A : Type i} {B : Type j}
  (g : ¬ A) →
  Inverse (resolve₂ {A = A} {B = B} g) inject₂
resolve₂-inject₂-inverse {A = A} {B = B} g = pair H K
  where
  H : inject₂ ∘ resolve₂ g ∼ identity {_} {A ＋ B}
  H (inject₁ x) = absurd x g
  H (inject₂ y) = reflexive

  K : RightInverse (resolve₂ g) inject₂
  K x = reflexive
```

= If a coproduct injection is an equivalences then the other component is empty <note:6aa2ace5-0120-4fb0-9681-1db6875a84c5>

#lemma(
    label: "69",
    supplement: cite_link(<rijke2025>, "Rijke 2025, exer. 11.1(c)")
)[
    If $inject1 ofType A -> A + B$ is an
    #link("note://32c2ca55-63ba-411b-9052-676a51fd16a1")[equivalence], then $B$
    is #link("note://16ffba35-7712-4eb7-8902-0812e529aa16")[empty]. Similarly,
    if $inject2 ofType B -> A + B$ is an equivalence, then $A$ is empty.
]
#proof[
    We prove the claim for $inject1$; the argument for $inject2$ is analogous.

    Suppose $inject1$ is an equivalence. Then
    #link("note://731be08a-a2ad-477a-8c08-d9f26c32de41")[it admits an inverse]
    function $g ofType A + B -> A$ together with
    #link("note://3cb1b8ca-2a77-4c8a-b726-ed8f10dfd208")[homotopies]
    $
        H ofType & g compose inject1 ~ id_(A), \
        K ofType & inject1 compose g ~ id_(A + B).
    $

    Suppose for contradiction that we are given an element $y ofType B$. Then
    applying homotopy $K$ to $inject2(y)$ yields a
    #link("note://261490cb-2887-4247-9a83-7f674e3c9651")[path]
    $
        inject1(g(inject2(y))) = inject2(y).
    $

    But this is impossible: by the
    #link("note://a58c0c4a-1fe6-4bf1-8aec-1cfc5ca262ee")[characterization of the
    identity types of coproducts], the type

    $
        inject1(x) = inject2(y)
    $
    is empty for any $x ofType A$ and $y ofType B$. Hence $B$ is empty.
]

See also #link("note://b7b0a00f-26af-486c-b13d-6f5160fbb2d0")[Lemma 6], which
shows the converse statement.

```agda
inject₁-isEquivalence→empty :
  {i j : Level} {A : Type i} {B : Type j} →
  IsEquivalence {B = A ＋ B} inject₁ →
  ¬ B
inject₁-isEquivalence→empty p y with isEquivalence→hasInverse p
... | (pair g (pair H K)) = project₁ (≃→↔ (＝≃Equal₁₂ (g (inject₂ y)) y)) q
  where
  q : inject₁ (g (inject₂ y)) ＝ inject₂ y
  q = K $ inject₂ y
  
inject₂-isEquivalence→empty : 
  {i j : Level} {A : Type i} {B : Type j} →
  IsEquivalence {B = A ＋ B} inject₂ →
  ¬ A
inject₂-isEquivalence→empty p x with isEquivalence→hasInverse p
... | (pair g (pair H K)) =
  project₁ (≃→↔ (＝≃Equal₂₁ x (g (inject₁ x)))) q
  where
  q : inject₂ (g (inject₁ x)) ＝ inject₁ x
  q = K (inject₁ x)
```

= Coproduct swap is its own inverse <note:2311a766-22a2-4a85-91f2-1f3bc032cfff>

#lemma(label: "7")[
    The functions $swap_(A, B) ofType A + B -> B + A$ and $swap_(B, A) ofType B
    + A -> A + B$ are
    #link("note://32c2ca55-63ba-411b-9052-676a51fd16a1")[inverses].
]

See #link("note://9ca63218-a429-4ee5-966c-89b4eb0c484f")[Coproduct swap] and
#link("note://001d31c7-7fb6-4878-883a-ff464bb9c0a8")[Coproduct type].

#proof[
    The #link("note://32c2ca55-63ba-411b-9052-676a51fd16a1")[relevant
    homotopies] hold #link("note://9ca63218-a429-4ee5-966c-89b4eb0c484f")[by
    definition].
]

Note, I didn't say that $swap$ is
#link("note://47767cc9-0064-45d3-8735-203b3236976d")[involutive], since it is
really a #link("note://b05d0e2e-b6ab-45ab-9277-9559f4ee5e1f")[family] of
functions indexed by the components of the coproduct. This means it isn't
involutive according to the
#link("note://47767cc9-0064-45d3-8735-203b3236976d")[technical definition I
gave], since the domain and codomain are different types. However, if you think
that's pedantic, then yeah it's basically an involution.

```agda
swapInverse :
  {i j : Level} {A : Type i} {B : Type j} →
  Inverse (swap {A = B} {B = A}) (swap {A = A} {B = B})
swapInverse = pair H H
  where
  H : {i j : Level} {A : Type i} {B : Type j} →
      (swap {A = B} {B = A}) ∘ (swap {A = A} {B = B}) ∼
      identity
  H (inject₁ x) = reflexive
  H (inject₂ x) = reflexive
```

= Left and right coproduct associate functions are inverses <note:9ef10dfd-e951-4cad-a7cb-beae239f4f2c>

#lemma(label: "8")[
    The left and right
    #link("note://001d31c7-7fb6-4878-883a-ff464bb9c0a8")[coproduct]
    #link("note://70f0207b-40b0-4f50-9184-f0226ae0d956")[associate functions]
    are #link("note://32c2ca55-63ba-411b-9052-676a51fd16a1")[inverses].
]
#proof[
    The #link("note://32c2ca55-63ba-411b-9052-676a51fd16a1")[relevant
    homotopies] hold #link("note://70f0207b-40b0-4f50-9184-f0226ae0d956")[by
    definition].
]
 
```agda
associateInverse :
  {i j k : Level} {A : Type i} {B : Type j} {C : Type k} →
  Inverse (associateˡ {A = A} {B = B} {C = C})
          (associateʳ {A = A} {B = B} {C = C})
associateInverse {A = A} {B = B} {C = C} = pair H K
  where
  H : associateʳ ∘ associateˡ ∼ (identity {_} {(A ＋ B) ＋ C})
  H (inject₁ (inject₁ x)) = reflexive
  H (inject₁ (inject₂ x)) = reflexive
  H (inject₂ x) = reflexive

  K : associateˡ ∘ associateʳ ∼ (identity {_} {A ＋ (B ＋ C)})
  K (inject₁ x) = reflexive
  K (inject₂ (inject₁ x)) = reflexive
  K (inject₂ (inject₂ x)) = reflexive
```

