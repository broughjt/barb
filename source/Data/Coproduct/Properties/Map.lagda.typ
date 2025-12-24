#import("../../../../../../library/template.typ"): *

#show: template

```agda
module Data.Coproduct.Properties.Map where

open import Base.Function.Core
open import Base.Function.Definitions
open import Base.Identity.Core
open import Base.Identity.Definitions hiding (_⁻¹; _∙_)
open import Base.Universe.Core
open import Data.Coproduct.Core
open import Data.Coproduct.Definitions
open import Data.Sigma.Core
```

= Coproduct map respects identity and composition <note:a9a759b6-a0c6-4bcf-a6ed-3e283ddc959c>
 
#lemma(
    label: "27",
    supplement: cite_link(<rijke2025>, "Rijke 2025, exer. 9.6(a-b)")
)[
    Given $f ofType A -> C$ and $g ofType B -> D$, let
    $
        f + g ofType A + B -> C + D
    $
    denote the #link("note://95fefab8-ba33-4759-8a33-03997164ebab")[map
    operation on coproducts]. Then

    1. For all types $A$ and $B$, there is a
       #link("note://3cb1b8ca-2a77-4c8a-b726-ed8f10dfd208")[homotopy]
       $
           id_(A) times id_(B) ~ id_(A times B)
       $
       (see #link("note://efea6413-096d-4249-8ef0-a4de74fcee13")[Identity
       function]).
    2. Given #link("note://bc9568f6-830b-4b4e-9aab-1808b1127cb0")[composable]
       functions
       $
           A -->^f & A' -->^f' & A'', \
           B -->^g & B' -->^g' & B''
       $
       there is a homotopy
       $
           (f' compose f) times (g' compose g) ~ (f' + g') times (f + g).
       $
]
#proof[
    The homotopies for both statements hold
    #link("note://95fefab8-ba33-4759-8a33-03997164ebab")[by definition].
]

```agda
mapIdentity : {i j : Level} {A : Type i} {B : Type j} →
                 map {A = A} {B = B} identity identity ∼ identity
mapIdentity (inject₁ x) = reflexive
mapIdentity (inject₂ y) = reflexive

mapCompose :
  {i j k l m n : Level}
  {A : Type i} {A' : Type j} {A'' : Type k}
  {B : Type l} {B' : Type m} {B'' : Type n}
  (f : A → A') (f' : A' → A'') (g : B → B') (g' : B' → B'') →
  map (f' ∘ f) (g' ∘ g) ∼ (map f' g') ∘ (map f g)
mapCompose f f' g g' (inject₁ x) = reflexive
mapCompose f f' g g' (inject₂ y) = reflexive
```

= Coproduct map respects homotopy <note:cd0f9173-bb5a-4065-9e6d-06639c5776e8>
 
#lemma(
    label: "28",
    supplement: cite_link(<rijke2025>, "Rijke 2025, exer. 9.6(c)")
)[
    Given $f ofType A -> C$ and $g ofType B -> D$, let
    $
        f + g ofType A + B -> C + D
    $
    denote the #link("note://95fefab8-ba33-4759-8a33-03997164ebab")[map
    operation on coproducts]. If there are
    #link("note://3cb1b8ca-2a77-4c8a-b726-ed8f10dfd208")[homotopies] $H ofType f
    ~ f'$ and $K ofType g ~ g'$, then there is a homotopy $(f + g) ~ (f' + g')$.
]
#proof[
    Let $u ofType A + B$. Our goal is to construct a path
    $
        (f + g)(u) ~ (f' + g')(u).
    $
    We proceed by case analysis. If we have $inject1(x) ofType A + B$ for some
    $x ofType A$, then the goal reduces to
    $
        inject1(f(x)) ~ inject1(f'(x)).
    $
    We can obtain such a homotopy by taking $ap_(inject1)(H(x))$ (see
    #link("note://7caf7ee0-9e2a-4761-bee9-25cd52820039")[Action on
    paths]). Otherwise, we have $inject2(y) ofType A + B$ for some $y ofType B$,
    and we can take $ap_(inject2)(K(y))$.
]

```agda
mapHomotopy : {i j k l : Level}
              {A : Type i} {B : Type j} {C : Type k} {D : Type l}
              {f f' : A → C} {g g' : B → D} →
              f ∼ f' → g ∼ g' → map f g ∼ map f' g'
mapHomotopy H K (inject₁ x) = pathAction inject₁ (H x)
mapHomotopy H K (inject₂ y) = pathAction inject₂ (K y) 
```

= Coproduct map of equivalences is an equivalence <note:9b0f68ff-9282-411d-bb37-14b00caf320d>
 
#lemma(supplement: cite_link(<rijke2025>, "Rijke 2025, exer. 9.6(d)"))[
    Given $f ofType A -> C$ and $g ofType B -> D$, let
    $
        f + g ofType A + B -> C + D
    $
    denote the #link("note://95fefab8-ba33-4759-8a33-03997164ebab")[map
    operation on coproducts]. If $f ofType A -> C$ and $g ofType B -> D$ are
    #link("note://32c2ca55-63ba-411b-9052-676a51fd16a1")[equivalences], then so
    is $f + g ofType A + B -> C + D$.
]
#proof[
    Let $f', f'' ofType C -> A$ be maps equipped with
    #link("note://3cb1b8ca-2a77-4c8a-b726-ed8f10dfd208")[homotopies] $H ofType f
    compose f' ~ id_(C)$ and $K ofType f'' compose f ~ id_(A)$. Similarly, let
    $g', g'' ofType D -> B$ be maps equipped with homotopies $L ofType g compose
    g' ~ id_(D)$ and $m ofType g'' compose g ~ id_(B)$.

    We construct a #link("note://32c2ca55-63ba-411b-9052-676a51fd16a1")[section]
    of $f + g$; constructing the corresponding
    #link("note://32c2ca55-63ba-411b-9052-676a51fd16a1")[retraction] is entirely
    analogous. #link("note://a9a759b6-a0c6-4bcf-a6ed-3e283ddc959c")[Lemma 27]
    shows that the coproduct map respects
    #link("note://bc9568f6-830b-4b4e-9aab-1808b1127cb0")[composition], so there
    is a homotopy
    $
        N ofType (f compose f') + (g compose g') ~ (f + g) compose (f' + g').
    $
    Since the coproduct map respects homotopies by
    #link("note://cd0f9173-bb5a-4065-9e6d-06639c5776e8")[Lemma 28], we also have
    $
        H + K ofType (f compose f') + (g compose g') ~ id_(C) + id_(D).
    $
    Finally, Lemma 27 also shows that the coproduct map respects the
    #link("note://efea6413-096d-4249-8ef0-a4de74fcee13")[identity map], so we
    have a homotopy
    $
        id_(C) + id_(D) ~ id_(C + D).
    $
    Combining these, we obtain a homotopy
    $
        (f + g) compose (f' + g') ~ id_(C + D)
    $
    witnessing that $f' + g'$ is a section of $f + g$.
]

```agda
mapEquivalence :
  {i j k l : Level}
  {A : Type i} {B : Type j} {C : Type k} {D : Type l}
  {f : A → C} {g : B → D} →
  IsEquivalence f → IsEquivalence g → IsEquivalence (map f g)
mapEquivalence {A = A} {B = B} {C = C} {D = D} {f = f} {g = g}
  (pair (pair f' H) (pair f'' K)) (pair (pair g' L) (pair g'' M)) =
  pair (pair (map f' g') O) (pair (map f'' g'') Q)
  where
  -- Note: This proof was written before I switched the definition of
  -- IsEquivalence to be Retraction f × Section f instead of Section f ×
  -- Retraction f, so it unfortunately doesn't correspond to the names in the
  -- paper proof.
  HL : map (f' ∘ f) (g' ∘ g) ∼ map (identity {_} {A}) (identity {_} {B})
  HL = mapHomotopy H L

  N : map (f' ∘ f) (g' ∘ g) ∼ map f' g' ∘ map f g
  N = mapCompose f f' g g'

  O : map f' g' ∘ map f g ∼ identity {_} {A ＋ B}
  O = (N ⁻¹) ∙ HL ∙ mapIdentity

  KM : map (f ∘ f'') (g ∘ g'') ∼ map (identity {_} {C}) (identity {_} {D})
  KM = mapHomotopy K M

  P : map (f ∘ f'') (g ∘ g'') ∼ map f g ∘ map f'' g''
  P = mapCompose f'' f g'' g

  Q : map f g ∘ map f'' g'' ∼ identity {_} {C ＋ D}
  Q = (P ⁻¹) ∙ KM ∙ mapIdentity
```
