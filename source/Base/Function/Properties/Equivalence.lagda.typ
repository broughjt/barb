#import("../../../../../../library/template.typ"): *

#show: template

```agda
module Base.Function.Properties.Equivalence where

open import Base.Function.Core
open import Base.Function.Definitions
open import Base.Identity.Core
open import Base.Universe.Core
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
identityIsEquivalence : {i : Level} {A : Type i} →
                      IsEquivalence (identity {_} {A})
identityIsEquivalence = let p = pair identity λ x → reflexive in pair p p
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

-- Getters

inverse→hasInverse : {i j : Level} {A : Type i} {B : Type j}
                     (f : A → B) (g : B → A) →
                     Inverse f g → HasInverse f
inverse→hasInverse f g p = pair g p

inverse→isEquivalence : {i j : Level} {A : Type i} {B : Type j}
                        (f : A → B) (g : B → A) →
                        Inverse f g → IsEquivalence f
inverse→isEquivalence f g p = hasInverse→isEquivalence (pair g p)

inverse→≃ : {i j : Level} {A : Type i} {B : Type j}
            (f : A → B) (g : B → A) →
            Inverse f g → A ≃ B
inverse→≃ f g p = pair f (inverse→isEquivalence f g p)
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
                 (f : A → B) (g : B → A) →
                 Inverse f g → Inverse g f
inverseInverse f g = Sigma.swap
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
... | (pair g q) = inverse→≃ g f (inverseInverse f g q)
```

= Sections and retractions are dual <note:608cfcd8-b127-4cde-a4ad-afcb1f38cccd>
 
#lemma[
    Consider two maps $f ofType A -> B$ and $g ofType B -> A$. If $g$ is a
    #link("note://32c2ca55-63ba-411b-9052-676a51fd16a1")[section] of $f$ then
    $f$ is #link("note://32c2ca55-63ba-411b-9052-676a51fd16a1")[retraction] of
    $g$, and if $g$ is a retraction of $f$ then $f$ is a section of $g$.
]
#proof[
    The function $g$ is a section of $f$ when it comes equipped with a
    #link("note://3cb1b8ca-2a77-4c8a-b726-ed8f10dfd208")[homotopy] $f compose g
    ~ id_(B)$, which is also the condition for $f$ being a retraction of
    $g$. Similarly, $g$ is a retraction of $f$ when there is a homotopy $g
    compose f ~ id_(A)$, which is also when $f$ is a section of $g$.
]

```agda
sectionRetraction : {i j : Level} {A : Type i} {B : Type j}
                    {f : A → B} {g : B → A} →
                    RightInverse f g → LeftInverse g f
sectionRetraction = identity

retractionSection : {i j : Level} {A : Type i} {B : Type j}
                    {f : A → B} {g : B → A} →
                    LeftInverse f g → RightInverse g f
retractionSection = identity
```

= Sections compose <note:28c89bbd-87da-42ef-b825-18c8ab632c2f>
 
#lemma(label: "20")[
    Let $f ofType A -> B$, $f' ofType B -> A$, $g ofType B -> C$, and $g' ofType
    C -> B$ be maps such that $f'$ is a
    #link("note://32c2ca55-63ba-411b-9052-676a51fd16a1")[section] of $f$ and
    $g'$ is a section of $g$. Then $f' compose g'$ is a section of $g compose f$.
]
#proof[
    #link("note://32c2ca55-63ba-411b-9052-676a51fd16a1")[By assumption], there
    are #link("note://3cb1b8ca-2a77-4c8a-b726-ed8f10dfd208")[homotopies]
    $
        F ofType & f compose f' ~ id_(B), \
        G ofType & g compose g' ~ id_(C).
    $
    #link("note://32c2ca55-63ba-411b-9052-676a51fd16a1")[Our goal] is to
    construct a homotopy
    $
        (g compose f) compose (f' compose g') ~ id_(C).
    $
    The #link("note://7805061a-565d-4412-9ca4-acb998e89555")[left whiskering]
    operation on $F$ by $g$ gives
    $
        g dot.op F ofType g compose f compose f' ~ g.
    $
    #link("note://7805061a-565d-4412-9ca4-acb998e89555")[Right whiskering] this
    homotopy by $g'$ gives
    $
        g dot.op F dot.op g' ofType
        g compose f compose f' compose g' ~ g compose g'.
    $
    Then #link("note://a3eaa21d-b0a4-4aed-80fd-ed5aeb914aab")[concatenation]
    with $G$ on the right gives
    $
        (g dot.op F dot.op g') dot.op G ofType
        g compose f compose f' compose g' ~ id_(C)
    $
    as needed.

]

```agda
sectionCompose : {i j k : Level} {A : Type i} {B : Type j} {C : Type k}
                 (g : B → C) (g' : C → B) (f : A → B) (f' : B → A) →
                 RightInverse g g' → RightInverse f f' →
                 RightInverse (g ∘ f) (f' ∘ g')
sectionCompose g g' f f' G F = g ∙ₗ F ∙ᵣ g' ∙ G
```

= Retractions compose <note:a6bb012d-cfaa-4fff-972c-dd70be453a5a>
 
#lemma(label: "21")[
    Let $f ofType A -> B$, $f' ofType B -> A$, $g ofType B -> C$, and $g' ofType
    C -> B$ be maps such that $f'$ is a
    #link("note://32c2ca55-63ba-411b-9052-676a51fd16a1")[retraction] of $f$ and
    $g'$ is a retraction of $g$. Then $f' compose g'$ is retraction of $g
    compose f$.
]
#proof[
    Analogous to the proof for
    #link("note://28c89bbd-87da-42ef-b825-18c8ab632c2f")[Lemma 20].
]

```agda
retractionCompose : {i j k : Level} {A : Type i} {B : Type j} {C : Type k}
                    (g : B → C) (g' : C → B) (f : A → B) (f' : B → A) →
                    LeftInverse g g' → LeftInverse f f' →
                    LeftInverse (g ∘ f) (f' ∘ g')
retractionCompose g g' f f' G F = (f' ∙ₗ G ∙ᵣ f)  ∙ F
```

= Inverse functions compose <note:6ba4ba4a-79ee-41cd-911d-f1ea3c0d9eea>

#lemma(label: "22")[
    If $f ofType A -> B$ and $f' ofType B -> A$ are
    #link("note://32c2ca55-63ba-411b-9052-676a51fd16a1")[inverses] and $g ofType
    B -> C$ and $g' ofType C -> B$ are inverses then $g compose f ofType A -> C$
    and $f' compose g' ofType C -> A$ are inverses.
]
#proof[
    By Lemmas #link("note://28c89bbd-87da-42ef-b825-18c8ab632c2f")[20] and
    #link("note://a6bb012d-cfaa-4fff-972c-dd70be453a5a")[21].
]

```agda
inverseCompose : {i j k : Level} {A : Type i} {B : Type j} {C : Type k}
                 (g : B → C) (g' : C → B) (f : A → B) (f' : B → A) →
                 Inverse g g' → Inverse f f' → Inverse (g ∘ f) (f' ∘ g')
inverseCompose g g' f f' (pair G G') (pair F F') = pair
  (retractionCompose g g' f f' G F)
  (sectionCompose g g' f f' G' F')
```

= Equivalences compose <note:7357b4f8-f609-47f1-8644-046018748ae7>

#corollary[
    If $g ofType B -> C$ and $f ofType A -> B$ are
    #link("note://32c2ca55-63ba-411b-9052-676a51fd16a1")[equivalences], then $g
    compose f ofType A -> C$ is an equivalence.
]
#proof[
    By #link("note://6ba4ba4a-79ee-41cd-911d-f1ea3c0d9eea")[Lemma 22].
]

```agda
isEquivalenceCompose :
  {i j k : Level} {A : Type i} {B : Type j} {C : Type k}
  (g : B → C) (f : A → B) →
  IsEquivalence g → IsEquivalence f → IsEquivalence (g ∘ f)
isEquivalenceCompose g f p q
  with isEquivalence→hasInverse p | isEquivalence→hasInverse q
... | pair g' p' | pair f' q' =
  inverse→isEquivalence (g ∘ f) (f' ∘ g') (inverseCompose g g' f f' p' q')

≃-compose : {i j k : Level} {A : Type i} {B : Type j} {C : Type k} →
            (B ≃ C) → (A ≃ B) → (A ≃ C)
≃-compose (pair g p) (pair f q) =
  pair (g ∘ f) (isEquivalenceCompose g f p q)
```

= Section and homotopic implies section <note:09a34157-9846-4e5c-bd5f-bb3b00926cd9>

#lemma(label: "23")[
    Let $g ofType B -> A$ be a
    #link("note://32c2ca55-63ba-411b-9052-676a51fd16a1")[section] of a function
    $f ofType A -> B$. If $f' ofType A -> B$ is another function equipped with a
    #link("note://3cb1b8ca-2a77-4c8a-b726-ed8f10dfd208")[homotopy] $f ~ f'$,
    then $g$ is also a section of $f'$. Similarly, if $g' ofType B -> A$ is a
    function equipped with a homotopy $g ~ g'$, then $g'$ is also a section of
    $f$.
]
#proof[
    We show the first statement; the second statement is analogous.

    #link("note://32c2ca55-63ba-411b-9052-676a51fd16a1")[By assumption] there
    are homotopies
    $
        G ofType & f compose g ~ id_(B), \
        H ofType & f ~ f'.
    $
    To construct a homotopy $f' compose g ~ id_(B)$, take the
    #link("note://926fa23f-6495-407a-a492-9aec9e451930")[inverse] of $H$
    $
        H^(-1) ofType f' ~ f,
    $
    #link("note://7805061a-565d-4412-9ca4-acb998e89555")[right whisker] with $g$
    $
        H^(-1) dot.op g ofType f' compose g ~ f compose g
    $
    and #link("note://a3eaa21d-b0a4-4aed-80fd-ed5aeb914aab")[concatentate] with
    $G$ on the right
    $
        (H^(-1) dot.op g) dot.op G ofType f' compose g ~ id_(B).
    $
]

```agda
section→homotopy→sectionˡ : {i j : Level} {A : Type i} {B : Type j}
                            {f f' : A → B} {g : B → A} →
                            RightInverse f g → f ∼ f' → RightInverse f' g
section→homotopy→sectionˡ {g = g} G H = (H ⁻¹) ∙ᵣ g ∙ G

section→homotopy→sectionʳ : {i j : Level} {A : Type i} {B : Type j}
                            {f : A → B} {g g' : B → A} →
                            RightInverse f g → g ∼ g' → RightInverse f g'
section→homotopy→sectionʳ {f = f} G H = (f ∙ₗ (H ⁻¹)) ∙ G
```

= Retraction and homotopic implies retraction <note:bc701147-fa84-4f61-a018-f767d6add99b>

#lemma(label: "24")[
    Let $g ofType B -> A$ be a
    #link("note://32c2ca55-63ba-411b-9052-676a51fd16a1")[retraction] of $f
    ofType A -> B$. If a map $f' ofType A -> B$ comes equipped with a
    #link("note://3cb1b8ca-2a77-4c8a-b726-ed8f10dfd208")[homotopy] $f ~ f'$,
    then $g$ is also a retraction of $f'$. Similarly, if a map $g' ofType B ->
    A$ comes equipped with a homotopy $g ~ g'$, then $g'$ is also a retraction
    of $f$.
]
#proof[
    Analogous to the proof for
    #link("note://09a34157-9846-4e5c-bd5f-bb3b00926cd9")[Lemma 23].
]

```agda
retraction→homotopy→retractionˡ : {i j : Level} {A : Type i} {B : Type j}
                                  {f f' : A → B} {g : B → A} →
                                  LeftInverse f g → f ∼ f' →
                                  LeftInverse f' g
retraction→homotopy→retractionˡ {g = g} G H = (g ∙ₗ (H ⁻¹)) ∙ G

retraction→homotopy→retractionʳ : {i j : Level} {A : Type i} {B : Type j}
                                  {f : A → B} {g g' : B → A} →
                                  LeftInverse f g → g ∼ g' →
                                  LeftInverse f g'
retraction→homotopy→retractionʳ {f = f} G H = ((H ⁻¹) ∙ᵣ f) ∙ G
```

= Inverse and homotopic implies inverse <note:52746242-840c-49cd-b924-5d5889004220>
 
#lemma(label: "25")[
    Let $g ofType B -> A$ be an
    #link("note://32c2ca55-63ba-411b-9052-676a51fd16a1")[inverse] to a function
    $f ofType A -> B$. If there is another function $f' ofType A -> B$ with a
    #link("note://3cb1b8ca-2a77-4c8a-b726-ed8f10dfd208")[homotopy] $f ~ f'$,
    then $f'$ and $g$ are inverses. Similarly, if there is another $g' ofType B
    -> A$ with a homotopy $g ~ g'$, then $f$ and $g'$ are inverses.
]
#proof[
    By Lemmas #link("note://09a34157-9846-4e5c-bd5f-bb3b00926cd9")[23] and
    #link("note://bc701147-fa84-4f61-a018-f767d6add99b")[24].
]

```agda
inverse→homotopy→inverseˡ : {i j : Level} {A : Type i} {B : Type j}
                            {f f' : A → B} {g : B → A} →
                            Inverse f g → f ∼ f' → Inverse f' g
inverse→homotopy→inverseˡ {f = f} {f' = f'} {g = g} (pair G H) K = pair
  (retraction→homotopy→retractionˡ {g = g} G K)
  (section→homotopy→sectionˡ H K)

inverse→homotopy→inverseʳ : {i j : Level} {A : Type i} {B : Type j}
                             {f : A → B} {g g' : B → A} →
                             Inverse f g → g ∼ g' → Inverse f g'
inverse→homotopy→inverseʳ {f = f} {g = g} {g' = g'} (pair G H) K = pair
  (retraction→homotopy→retractionʳ G K)
  (section→homotopy→sectionʳ {f = f} H K)
```

= Equivalence and homotopic implies equivalence <note:4b08592f-f5db-4f89-a80d-450239d5889c>
 
#lemma(supplement: cite_link(<rijke2025>, "Rijke 2025, exer. 9.3(a)"))[
    Let $f, f' ofType A -> B$ be maps equipped with a
    #link("note://3cb1b8ca-2a77-4c8a-b726-ed8f10dfd208")[homotopy] $f ~ f'$. Then
    $f$ is an #link("note://32c2ca55-63ba-411b-9052-676a51fd16a1")[equivalence]
    if and only if $f'$ is an equivalence.
]
#proof[
    It suffices to prove one direction only, since the other then follows by
    #link("note://926fa23f-6495-407a-a492-9aec9e451930")[inverting] the
    homotopy. A map is an
    #link("note://32c2ca55-63ba-411b-9052-676a51fd16a1")[equivalence] if it has
    both a #link("note://32c2ca55-63ba-411b-9052-676a51fd16a1")[section] and a
    #link("note://32c2ca55-63ba-411b-9052-676a51fd16a1")[retraction]. Since this
    holds for $f$, and Lemmas
    #link("note://09a34157-9846-4e5c-bd5f-bb3b00926cd9")[23] and
    #link("note://bc701147-fa84-4f61-a018-f767d6add99b")[24] shows these
    concepts are invariant under homotopy, it follows that $f'$ is also an
    equivalence.
]

```agda
isEquivalence→homotopy→isEquivalence :
  {i j : Level} {A : Type i} {B : Type j}
  {f f' : A → B} →
  IsEquivalence f → f ∼ f' → IsEquivalence f'
isEquivalence→homotopy→isEquivalence (pair (pair g G) (pair h H)) L = pair
  (pair g (section→homotopy→sectionˡ G L))
  (pair h (retraction→homotopy→retractionˡ {g = h} H L))

homotopy→isEquivalence↔isEquivalence :
  {i j : Level} {A : Type i} {B : Type j}
  {f f' : A → B} →
  f ∼ f' → 
  IsEquivalence f ↔ IsEquivalence f'
homotopy→isEquivalence↔isEquivalence H =
  pair (flip isEquivalence→homotopy→isEquivalence H)
       (flip isEquivalence→homotopy→isEquivalence (H ⁻¹))
```

= Equivalent implies logically equivalent <note:c03e918e-a39a-46c0-8c2b-84e2f1bbb97c>
 
#lemma[
    Let $A$ and $B$ be types. If $A$ and $B$ are
    #link("note://32c2ca55-63ba-411b-9052-676a51fd16a1")[equivalent] then $A$
    and $B$ are #link("note://27061ddb-2091-46c1-8752-21db2ab57f44")[logically
    equivalent]. In symbols, if $A tilde.eq B$ then $A arrow.l.r B$.
]
#proof[
    #link("note://32c2ca55-63ba-411b-9052-676a51fd16a1")[By the definition of
     equivalence] there are maps back and forth.
]

```agda
≃→↔ : {i j : Level} {A : Type i} {B : Type j} →
      (A ≃ B) → (A ↔ B)
≃→↔ (pair f (pair (pair g _) _)) = pair f g
```

= Commutative triangle with section lemma <note:b92b0253-66cd-46ff-aaab-8c33541cfd45>
 
#lemma(supplement: cite_link(<rijke2025>, "Rijke 2025, exer. 9.4(a)"))[
    Consider a commuting triangle
    #figure(
        diagram($
            A edge("rr", h, ->) edge("dr", f, ->, label-side: #right) & & B edge("dl", g, ->, label-side: #left) \
                & C
        $)
    )
    with $H ofType f ~ g compose h$. If $h$ has a
    #link("note://32c2ca55-63ba-411b-9052-676a51fd16a1")[section] $s ofType B ->
    A$, then the triangle
    #figure(
        diagram($
            B edge("rr", s, ->) edge("dr", g, ->, label-side: #right) & & A edge("dl", f, ->, label-side: #left) \
                & C
        $)
    )
    commutes, and $f$ has a section if and only if $g$ has a section.
]
#proof[
    *Step 1 (Commutativity).* Suppose $h ofType A -> B$ has a section $s ofType
    B -> A$ equipped with a homotopy $K ofType h compose s ~ id_(B)$. To show
    the triangle commutes, we need to construct a
    #link("note://3cb1b8ca-2a77-4c8a-b726-ed8f10dfd208")[homotopy] $S ofType g ~
    f compose
    s$. #link("note://7805061a-565d-4412-9ca4-acb998e89555")[Whiskering] on $H$
    the right by $s$ gives
    $
        H dot.op s ofType & f compose s ~ (g compose h) compose s
    $
    and whiskering $K$ on the left by $g$ gives
    $
        (g compose h) compose s ~ g.
    $
    Thus, we can obtain $S$ by
    #link("note://a3eaa21d-b0a4-4aed-80fd-ed5aeb914aab")[concatenating] these
    two and then taking their
    #link("note://926fa23f-6495-407a-a492-9aec9e451930")[inverse].

    *Step 2 ($==>$).* Next, suppose $f ofType A -> X$ has a section $t ofType X
    -> A$ equipped with $T ofType f compose t ~ id_(X)$. Then we can obtain a
    homotopy $U ofType g compose (h compose t) ~ id_(X)$ by right whiskering $H$
    with $t$
    $
        H dot.op t ofType f compose t ~ (g compose h) compose t,
    $
    taking the inverse
    $
        (H dot.op t)^(-1) ofType (g compose h) compose t ~ f compose t,
    $
    and concatenating with $T$
    $
        (H dot.op t)^(-1) dot.op T ofType g compose (h compose t) ~ id_(X).
    $
    Therefore $h compose t$ is a section of $g$.

    *Step 3 ($<==$).* Finally, suppose $g ofType B -> X$ has a section $u ofType
    X -> B$ equipped with $U ofType g compose u ~ id_(X)$. First, we can obtain
    a homotopy $S^(-1) ofType f compose s ~ g$ by inverting the homotopy $S$
    from Step 1. Whiskering on $S$ on the right by $u$ gives
    $
        S^(-1) dot.op u ofType f compose s compose u ~ g compose u.
    $
    Therefore by concatenating on the right by $U$ we obtain
    $
        (S^(-1) dot.op u) dot.op U ofType f compose s compose u ~ id_(X),
    $
    and hence $s compose u$ is a section of $f$.
]

```agda
sectionTriangle :
  {i j k : Level} {A : Type i} {B : Type j} {X : Type k}
  (f : A → X) (g : B → X) (h : A → B) (s : B → A) →
  f ∼ g ∘ h → RightInverse h s → g ∼ f ∘ s
sectionTriangle f g h s H K = (L ∙ M) ⁻¹
  where
  L : f ∘ s ∼ (g ∘ h) ∘ s
  L = H ∙ᵣ s

  M : (g ∘ h) ∘ s ∼ g
  M = g ∙ₗ K

sectionTop→left→right :
  {i j k : Level} {A : Type i} {B : Type j} {X : Type k}
  (f : A → X) (g : B → X) (h : A → B) →
  f ∼ g ∘ h → Section h → Section f → Section g
sectionTop→left→right {X = X} f g h H (pair s S) (pair t T) =
  pair (h ∘ t) U
  where
  U : g ∘ (h ∘ t) ∼ identity {_} {X}
  U = (H ∙ᵣ t) ⁻¹ ∙ T

sectionTop→right→left :
  {i j k : Level} {A : Type i} {B : Type j} {X : Type k}
  (f : A → X) (g : B → X) (h : A → B) →
  f ∼ g ∘ h → Section h → Section g → Section f
sectionTop→right→left f g h H (pair s S) (pair u U) =
  pair (s ∘ u) (S' ⁻¹ ∙ᵣ u ∙ U)
  where
  S' : g ∼ f ∘ s
  S' = sectionTriangle f g h s H S

sectionTop→left↔right :
  {i j k : Level} {A : Type i} {B : Type j} {X : Type k}
  (f : A → X) (g : B → X) (h : A → B) →
  f ∼ g ∘ h → Section h → (Section f ↔ Section g)
sectionTop→left↔right f g h H p =
  pair (sectionTop→left→right f g h H p)
       (sectionTop→right→left f g h H p)
```

= Commutative triangle with retraction lemma <note:92588128-5591-45a6-9559-c75e846fde57>
 
#lemma(supplement: cite_link(<rijke2025>, "Rijke 2025, exer. 9.4(b)"))[
    Consider a commuting triangle
    #figure(
        diagram($
            A edge("rr", h, ->) edge("dr", f, ->, label-side: #right) & & B edge("dl", g, ->, label-side: #left) \
                & X
        $)
    )
    with $H ofType f ~ g compose h$. If $g ofType B -> X$ has a
    #link("note://32c2ca55-63ba-411b-9052-676a51fd16a1")[retraction] $r ofType X
    -> B$, then the triangle
    #figure(
        diagram($
            A edge("rr", f, ->) edge("dr", h, ->, label-side: #right) & & X edge("dl", r, ->, label-side: #left) \
                & B
        $)
    )
    commutes, and $f ofType A -> X$ has a retraction if and only if $h ofType A
    -> B$ has a retraction.
]
#proof[
    *Step 1 (Commutativity).* Let $R ofType r compose g ~ id_(B)$ witness that
    $r ofType X -> B$ is a retraction of $g ofType B -> X$. Then we can
    construct a #link("note://3cb1b8ca-2a77-4c8a-b726-ed8f10dfd208")[homotopy]
    $S ofType h ~ r compose f$ by whiskering $H$ on the left by $r$ $ r dot.op H
    ofType r compose f ~ r compose g compose h, $ whiskering $R$ on the right by
    $h$
    $
        R dot.op h ofType r dot.op g dot.op h ~ h,
    $
    and then #link("note://a3eaa21d-b0a4-4aed-80fd-ed5aeb914aab")[concatenating]
    these two homotopies and taking their
    #link("note://926fa23f-6495-407a-a492-9aec9e451930")[inverse].

    *Step 2 ($==>$).* Suppose $s ofType X -> A$ is a retraction of $f ofType X
    -> A$, with $S ofType s compose f ~ id_(A)$. Whiskering $H^(-1)$ on the left
    by $s$ gives
    $
        s dot.op H^(-1) ofType s compose g compose h ~ s compose f.
    $
    Concatenating this with $S$ then gives
    $
        (s dot.op H^(-1)) dot.op S ofType (s compose g) compose h ~ id_(A).
    $
    Therefore $s compose g$ is a retraction of $h$.

    *Step 3 ($<==$).* Now let $t ofType B -> A$ be a section of $h ofType A ->
    B$ equipped with a homotopy $T ofType t compose h ~ id_(A)$. Whiskering the
    inverse of the homotopy $S ofType h ~ r compose f$ constructed in Step 1 on
    the left by $t$ gives
    $
        t compose r compose f ~ t compose h.
    $
    Then concatenating on the right by $T ofType t compose h ~ id_(A)$ gives
    $
        (t compose r) compose f ~ id_(A).
    $
    Therefore $t compose r$ is a retraction of $f$.
]

```agda
retractionTriangle :
  {i j k : Level} {A : Type i} {B : Type j} {X : Type k}
  (f : A → X) (g : B → X) (h : A → B) (r : X → B) →
  f ∼ g ∘ h → LeftInverse g r → h ∼ r ∘ f
retractionTriangle f g h r H R = ((r ∙ₗ H) ∙ (R ∙ᵣ h)) ⁻¹

retractionRight→left→top :
  {i j k : Level} {A : Type i} {B : Type j} {X : Type k}
  (f : A → X) (g : B → X) (h : A → B) →
  f ∼ g ∘ h → Retraction g → Retraction f → Retraction h
retractionRight→left→top f g h H (pair r R) (pair s S) =
  pair (s ∘ g) (s ∙ₗ (H ⁻¹) ∙ S)

retractionRight→top→left :
  {i j k : Level} {A : Type i} {B : Type j} {X : Type k}
  (f : A → X) (g : B → X) (h : A → B) →
  f ∼ g ∘ h → Retraction g → Retraction h → Retraction f
retractionRight→top→left f g h H (pair r R) (pair t T) =
  pair (t ∘ r) (t ∙ₗ S ⁻¹ ∙ T)
  where
  S : h ∼ r ∘ f
  S = retractionTriangle f g h r H R

retractionRight→left↔top :
  {i j k : Level} {A : Type i} {B : Type j} {X : Type k}
  (f : A → X) (g : B → X) (h : A → B) →
  f ∼ g ∘ h → Retraction g → Retraction f ↔ Retraction h
retractionRight→left↔top f g h H p =
  pair (retractionRight→left→top f g h H p)
       (retractionRight→top→left f g h H p)
```

= Three for two property for equivalences <note:eb0e793e-d04a-4145-ad54-152aa50d2aee>
 
#theorem(
    supplement: [$3$-for-$2$ property for equivalences; #cite_link(<rijke2025>, "Rijke 2025, exer. 9.4(c)")]
)[
    If any two of the functions in the commutative diagram
    #figure(
        diagram($
            A edge("rr", h, ->) edge("dr", f, ->, label-side: #right) & & B edge("dl", g, ->, label-side: #left) \
                & X
        $)
    )
    are #link("note://32c2ca55-63ba-411b-9052-676a51fd16a1")[equivalences], then
    so is the third.
]
#proof[
    In each case, express the target function as a
    #link("note://bc9568f6-830b-4b4e-9aab-1808b1127cb0")[composition] of
    inverses and then apply
    #link("note://6ba4ba4a-79ee-41cd-911d-f1ea3c0d9eea")[Lemma 22] (which shows
    that inverses compose) and
    #link("note://52746242-840c-49cd-b924-5d5889004220")[Lemma 25] (which shows
    that inverses are invariant under homotopy).
]

```agda
isEquivalenceTop→left→right :
  {i j k : Level} {A : Type i} {B : Type j} {X : Type k}
  (f : A → X) (g : B → X) (h : A → B) →
  f ∼ g ∘ h → IsEquivalence h → IsEquivalence f → IsEquivalence g
isEquivalenceTop→left→right f g h H φ ψ with
  isEquivalence→hasInverse φ | isEquivalence→hasInverse ψ
... | (pair s φ') | (pair t ψ') = inverse→isEquivalence g (h ∘ t) ρ
  where
  ω : Inverse s h
  ω = inverseInverse h s φ'

  χ : Inverse (f ∘ s) (h ∘ t)
  χ = inverseCompose f t s h ψ' ω

  π : g ∼ f ∘ s
  π = sectionTriangle f g h s H (project₂ φ')

  ρ : Inverse g (h ∘ t)
  ρ = inverse→homotopy→inverseˡ χ (π ⁻¹)

isEquivalenceTop→right→left :
  {i j k : Level} {A : Type i} {B : Type j} {X : Type k}
  (f : A → X) (g : B → X) (h : A → B) →
  f ∼ g ∘ h → IsEquivalence h → IsEquivalence g → IsEquivalence f
isEquivalenceTop→right→left f g h H φ ψ with
  isEquivalence→hasInverse φ | isEquivalence→hasInverse ψ
... | (pair s φ') | (pair u ψ') = inverse→isEquivalence f (s ∘ u) χ
  where
  ω : Inverse (g ∘ h) (s ∘ u)
  ω = inverseCompose g u h s ψ' φ'

  χ : Inverse f (s ∘ u)
  χ = inverse→homotopy→inverseˡ ω (H ⁻¹)

isEquivalenceLeft→right→top : 
  {i j k : Level} {A : Type i} {B : Type j} {X : Type k}
  (f : A → X) (g : B → X) (h : A → B) →
  f ∼ g ∘ h → IsEquivalence f → IsEquivalence g → IsEquivalence h
isEquivalenceLeft→right→top f g h H φ ψ with
  isEquivalence→hasInverse φ | isEquivalence→hasInverse ψ
... | (pair t φ') | (pair u ψ') = inverse→isEquivalence h (t ∘ g) π
  where
  ψ'' : Inverse u g
  ψ'' = inverseInverse g u ψ'
                           
  ω : Inverse (u ∘ f) (t ∘ g)
  ω = inverseCompose u g f t ψ'' φ'
                                 
  χ : h ∼ u ∘ f
  χ = retractionTriangle f g h u H (project₁ ψ')
                                             
  π : Inverse h (t ∘ g)
  π = inverse→homotopy→inverseˡ ω (χ ⁻¹)
```
