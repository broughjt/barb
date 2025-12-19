#import("../../../../../../library/template.typ"): *

#show: template

```agda
module Data.Coproduct.Properties.Negation where

open import Base.Function.Core
open import Base.Function.Definitions
open import Base.Function.Negation
open import Base.Universe
open import Base.Identity.Core
open import Data.Coproduct.Core
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
