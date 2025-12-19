#import("../../../../../../library/template.typ"): *

#show: template

```agda
module Base.Function.Properties.Equivalence where

open import Base.Function.Core
open import Base.Function.Definitions
open import Base.Identity.Core
open import Base.Universe
open import Data.Sigma.Core
open import Data.Sigma.Definitions as Sigma
```

= The identity map is an equivalence <note:f00d5782-6e4f-4356-80ca-6e02baaf09ac>
 
#lemma(supplement: cite_link(<rijke2025>, "Rijke 2025, ex. 9.2.3"))[
    The #link("note://efea6413-096d-4249-8ef0-a4de74fcee13")[identity map] is an
    #link("note://32c2ca55-63ba-411b-9052-676a51fd16a1")[equivalence] for any
    type $A$.
]
#proof[
    The identity map is its own
    #link("note://32c2ca55-63ba-411b-9052-676a51fd16a1")[section] and
    #link("note://32c2ca55-63ba-411b-9052-676a51fd16a1")[retraction]. Checking
    this amounts to constructing a
    #link("note://3cb1b8ca-2a77-4c8a-b726-ed8f10dfd208")[homotopy]
    $
        id_(A) compose id_(A) ~ id_(A),
    $
    which covers both the section and retraction cases. Since
    $
        (id_(A) compose id_(A))(x) = id_(A)(x)
    $
    holds #link("note://a0baf580-5da2-4328-bfbd-202bedf37747")[judgementally]
    for each $x ofType A$, we can take $lambda x . refl_(x) ofType id_(A)
    compose id_(A) ~ id_(A)$.
]

```agda
identityEquivalence : {i : Level} {A : Type i} →
                      IsEquivalence (identity {_} {A})
identityEquivalence = let p = pair identity λ x → reflexive in pair p p
```

= If a function has both a section and a retraction then the section and retraction are homotopic <note:1eff33a2-4cba-48c0-8d40-19bf2c5d08ca>
 
#lemma(label: "2")[
    If a function $f ofType A -> B$ has both a
    #link("note://32c2ca55-63ba-411b-9052-676a51fd16a1")[section] $g ofType B ->
    A$ and a #link("note://32c2ca55-63ba-411b-9052-676a51fd16a1")[retraction] $h
    ofType B -> A$ then there is a
    #link("note://3cb1b8ca-2a77-4c8a-b726-ed8f10dfd208")[homotopy] $g ~ h$.
]
#proof[
    By assumption, we have
    #link("note://3cb1b8ca-2a77-4c8a-b726-ed8f10dfd208")[homotopies]
    $
        G ofType & f compose g ~ id_(B), \
        H ofType & h compose f ~ id_(A).
    $
    We need to construct a homotopy $g ~ h$. The
    #link("note://7805061a-565d-4412-9ca4-acb998e89555")[right whiskering]
    operation on $H$ by $g$ gives
    $
        H dot.op g ofType (h compose f) compose g ~ id_(A) compose g,
    $
    while the #link("note://7805061a-565d-4412-9ca4-acb998e89555")[left
    whiskering] operation on $G$ by $h$ gives
    $
        h dot.op G ofType h compose (f compose g) ~ h compose id_(B).
    $
    By the #link("note://2bb9c32b-d3eb-4693-a814-c37b23aac880")[associativity],
    #link("note://061ca7df-33a7-40f0-95ba-bb4f36a69e98")[unit laws], and
    #link("note://a3eaa21d-b0a4-4aed-80fd-ed5aeb914aab")[concatenation] of
    homotopies, we obtain a homotopy $g ~ h$.
]

I'm #link("note://5820f7b2-6d86-4af6-826c-e13c6ccc382f")[confused about why Agda
doesn't require me to use the associativity and unit laws for homotopy here], so
I sort of fudged the last line of this proof, otherwise I would be more
explicit.

```agda
sectionRetractionHomotopy : {i j : Level} {A : Type i} {B : Type j}
                            {f : A → B} {g h : B → A} →
                            RightInverse f g → LeftInverse f h → g ∼ h
sectionRetractionHomotopy {g = g} {h = h} G H = (H ∙ᵣ g) ⁻¹ ∙ (h ∙ₗ G)
```

= Has inverse if and only if equivalence <note:731be08a-a2ad-477a-8c08-d9f26c32de41>
 
#lemma(label: "3", supplement: cite_link(<rijke2025>, "Rijke 2025, prop. 9.2.7"))[
    A function #link("note://32c2ca55-63ba-411b-9052-676a51fd16a1")[has an
    inverse] if and only if it is an
    #link("note://32c2ca55-63ba-411b-9052-676a51fd16a1")[equivalence].
]
#proof[
    ($==>$) If a function $f ofType A -> B$ has an inverse $g ofType B -> A$,
    then it serves as both the
    #link("note://32c2ca55-63ba-411b-9052-676a51fd16a1")[section] and
    #link("note://32c2ca55-63ba-411b-9052-676a51fd16a1")[retraction] in the
    definition of equivalence.

    ($<==$) Let $f ofType A -> B$ be a function with a section $g ofType B -> A$
    and a retraction $h ofType B -> A$. Then there exist
    #link("note://3cb1b8ca-2a77-4c8a-b726-ed8f10dfd208")[homotopies]
    $
        G ofType & f compose g ~ id_(B), \
        H ofType & h compose f ~ id_(A).
    $
    Using $G$ and $H$,
    #link("note://1eff33a2-4cba-48c0-8d40-19bf2c5d08ca")[Lemma 2] shows that
    there is a homotopy $K ofType g ~ h$. Then the
    #link("note://7805061a-565d-4412-9ca4-acb998e89555")[right whiskering]
    operation on $K$ by $f$ gives
    $
        K dot.op f ofType g compose f ~ h compose f.
    $
    #link("note://a3eaa21d-b0a4-4aed-80fd-ed5aeb914aab")[Concatenating] this
    with $H$, we obtain
    $
        (K dot.op f) dot.op H ofType g compose f ~ id_(A).
    $
    Therefore, in addition to being a section of $f$, the map $g$ is also a
    retraction of $f$, and hence $g$ is an inverse of $f$.
]

See #link("note://37062ad9-51f7-43c6-b291-336dbf2ba460")[What is the explanation
for equivalence being a property while has inverse is a structure?] and
#link("note://08e31f3c-a922-4f1e-a708-6bf6e072e787")[Equivalence and has inverse
are logically equivalent but non-equivalent types].

```agda
hasInverse→isEquivalence : {i j : Level} {A : Type i} {B : Type j}
                           {f : A → B} → 
                           HasInverse f → IsEquivalence f
hasInverse→isEquivalence (pair g (pair G H)) = pair (pair g H) (pair g G)

isEquivalence→hasInverse : {i j : Level} {A : Type i} {B : Type j}
                           {f : A → B} →
                           IsEquivalence {A = A} {B = B} f → HasInverse f
isEquivalence→hasInverse {f = f} (pair (pair g G) (pair h H)) =
  pair g (pair L G)
  where
  K : g ∼ h
  K = sectionRetractionHomotopy G H

  L : LeftInverse f g
  L = (K ∙ᵣ f) ∙ H
       
hasInverse↔isEquivalence : {i j : Level} {A : Type i} {B : Type j}
                           {f : A → B} →
                           HasInverse f ↔ IsEquivalence f
hasInverse↔isEquivalence =
  pair hasInverse→isEquivalence isEquivalence→hasInverse
```

= Inverse inverse <note:b46b5dcc-963a-471f-9088-8872ed6a88c2>
 
#lemma(label: "4")[
    Let $f ofType A -> B$ and $g ofType B -> A$ be maps. If $g$ is an
    #link("note://32c2ca55-63ba-411b-9052-676a51fd16a1")[inverse] of $f$ then
    $f$ is an inverse of $g$.
]
#proof[
    Swap the #link("note://3cb1b8ca-2a77-4c8a-b726-ed8f10dfd208")[homotopies] in
    the #link("note://32c2ca55-63ba-411b-9052-676a51fd16a1")[definition of
    inverse].
]

```agda
inverseInverse : {i j : Level} {A : Type i} {B : Type j}
                 {f : A → B} {g : B → A} →
                 Inverse f g → Inverse g f
inverseInverse = Sigma.swap
```

= Inverse of an equivalence <note:b659d823-d985-4d50-bd63-416ecd1a107b>
 
#corollary(supplement: cite_link(<rijke2025>, "Rijke 2025, cor. 9.2.8"))[
    Let $A$ and $B$ be types. If $A tilde.eq B$ then $B tilde.eq A$.
]
#proof[
    Let $(f, p) ofType A tilde.eq B$. By
    #link("note://731be08a-a2ad-477a-8c08-d9f26c32de41")[Lemma 3], the map $f
    ofType A -> B$ has an
    #link("note://32c2ca55-63ba-411b-9052-676a51fd16a1")[inverse] $g ofType B ->
    A$. Reversing, the map $f$ is an inverse of $g$ by
    #link("note://b46b5dcc-963a-471f-9088-8872ed6a88c2")[Lemma 4]. By Lemma 3
    again, this holds only if $g$ is an
    #link("note://32c2ca55-63ba-411b-9052-676a51fd16a1")[equivalence], and hence
    the type $A tilde.eq B$ is inhabited.
]

See #link("note://32c2ca55-63ba-411b-9052-676a51fd16a1")[Sections, retractions,
inverses, and equivalences].

```agda
≃-inverse : {i j : Level} {A : Type i} {B : Type j} →
            A ≃ B → B ≃ A
≃-inverse (pair f p) with isEquivalence→hasInverse p
... | (pair g q) =
  pair g (hasInverse→isEquivalence (pair f (inverseInverse {f = f} {g = g} q))) 
```
