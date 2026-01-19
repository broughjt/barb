#import("../../../../../../library/template.typ"): *

#show: template

```agda
module Base.Function.Properties.Embedding where

open import Base.Function.Core
open import Base.Function.Definitions
open import Base.Function.Properties.Contractible
open import Base.Function.Properties.Equivalence
open import Base.Function.Properties.Fiber2
open import Base.Identity.Core
open import Base.Identity.Definitions hiding (_⁻¹)
open import Base.Identity.Properties
open import Base.Truncation.Definitions
open import Base.Truncation.Properties.Contractible
open import Base.Universe.Core
open import Data.Sigma.Core
open import Data.Sigma.Definitions
open import Data.Sigma.Properties.Equivalence
open import Data.Sigma.Properties.Identity
```

= Every equivalence is an embedding <note:577a5656-7132-434f-ba99-a2736940d780>
 
#theorem(
    label: "76",
    supplement: cite_link(<rijke2025>, "Rijke 2025, thm. 11.4.2")
)[
    Every #link("note://32c2ca55-63ba-411b-9052-676a51fd16a1")[equivalence] is
    an #link("note://cce94748-d9b3-4795-a3d8-c698b6dff9dd")[embedding].
]
#proof[
    Let $f ofType A -> B$ be an equivalence, and fix $x ofType A$. To show that
    $f$ is an embedding, we need to show that the
    #link("note://7caf7ee0-9e2a-4761-bee9-25cd52820039")[action on paths]

    $
        (x = y) -> (f(x) = f(y))
    $

    is an equivalence for each $y ofType A$. By the
    #link("note://47c2a4df-e0c1-49a6-8ce8-feae75d30105")[fundamental theorem of
    identity types], it suffices to prove that the type

    $
        sigmaType(y, A) f(x) = f(y)
    $

    is #link("note://f817901c-750e-4575-a259-d83730424ade")[contractible]. Since
    $f$ is an equivalence, each of its
    #link("note://96d1fb9a-fd38-48cc-886f-7643637ac1e7")[fibers] is contractible
    by #link("note://984c33bd-7fb6-4432-a0de-ddc279bddc1c")[Theorem 41]. In
    particular,

    $
        Fiber_(f)(f(x)) dot(eq) sigmaType(y, A) f(y) = f(x)
    $

    is contractible. By
    #link("note://215dd04d-4936-402a-86d1-a6c440ce962a")[Lemma 52], this fiber
    is equivalent to $sigmaType(y, A) f(x) = f(y)$. As contractibility is
    preserved under equivalence by
    #link("note://41aea79b-658b-464d-b9c4-0326602aa2db")[Lemma 42], it follows
    that $sigmaType(y, A) f(x) = f(y)$ is contractible.

    Hence the action on paths is an equivalence for every $x, y ofType A$, and
    therefore $f$ is an embedding.
]

```agda
isEquivalence→isEmbedding :
  {i j : Level} {A : Type i} {B : Type j}
  {f : A → B} →
  IsEquivalence f → IsEmbedding f
isEquivalence→isEmbedding {A = A} {f = f} p x =
  totalIsContractible→characterize-＝ r x (λ y → pathAction f)
  where
  q : IsContractible (Fiber f (f x))
  q = isEquivalence→isContractibleFunction p (f x)

  r : IsContractible (Σ A (λ y → f x ＝ f y))
  r = isEquivalence→isContractible→isContractible₁
      (fiber⁻¹ f x)
        (fiber⁻¹-isEquivalence f x)
        q
```

= Embeddings respect homotopy <note:577d40af-e9a0-4e3e-891e-003b1fdc88ff>

#lemma(
    label: "74",
    supplement: cite_link(<rijke2025>, "Rijke 2025, exer. 11.3")
)[
    Let $f, f' ofType piType(x, A) B(x)$ be functions. If there is a
    #link("note://3cb1b8ca-2a77-4c8a-b726-ed8f10dfd208")[homotopy] $f ~ f'$ then
    $f$ is an #link("note://cce94748-d9b3-4795-a3d8-c698b6dff9dd")[embedding] if
    and only if $f'$ is an embedding.
]
#proof[
    It suffices to prove one direction, since the converse follows by applying
    the same argument to $H^(-1)$.

    Suppose $f$ is an embedding and fix $x ofType A$. By the
    #link("note://47c2a4df-e0c1-49a6-8ce8-feae75d30105")[fundamental theorem of
    identity types], the
    #link("note://ae098784-7572-4d29-b548-a2db9b6d004a")[total space]
    $
        sigmaType(y, A) f(x) = f(y)
    $
    is #link("note://f817901c-750e-4575-a259-d83730424ade")[contractible].

    We define a map
    $
        h ofType sigmaType(y, A) f(x) = f(y) -> sigmaType(y, A) f'(x) = f'(y)
    $
    as the #link("note://bc9568f6-830b-4b4e-9aab-1808b1127cb0")[composite]
    $
        sigmaType(y, A) f(x) = f(y) & -->^(tilde.eq) Fiber_(f)(f(x)) \
            & -->^(tilde.eq) Fiber_(f')(f(x)) \
            & -->^(tilde.eq) Fiber_(f')(f'(x)) \
            & -->^(tilde.eq) sigmaType(y, A) f'(x) = f'(y).
    $
    Here:
    - the first and last equivalences are given by
      #link("note://215dd04d-4936-402a-86d1-a6c440ce962a")[Lemma 52],
    - the second is induced by the homotopy $H$
      (#link("note://87f106a8-6338-4411-940e-1b13aa3ccad7")[Lemma 71]),
    - and the third is given by
      #link("note://1229c654-047b-4517-9f4c-df4c03224d02")[transport] along the
      path $H(x) ofType f(x) = f'(x)$, which is an equivalence by
      #link("note://985f36e7-d07e-4742-ac8c-b7c0dfe1def8")[Lemma 37].
    Since each map is an equivalence, the composite $h$ is an equivalence by
    #link("note://7357b4f8-f609-47f1-8644-046018748ae7")[Lemma 56]. Therefore,
    since contractibility is preserved by equivalence
    (#link("note://41aea79b-658b-464d-b9c4-0326602aa2db")[Lemma 42]), it follows
    that
    $
        sigmaType(y, A) f'(x) = f'(y)
    $
    is contractible.

    By the #link("note://47c2a4df-e0c1-49a6-8ce8-feae75d30105")[fundamental
    theorem of identity types], this implies that the family
    $
        piType(y, A) x = y -> f'(x) = f'(y)
    $
    given by the action on paths by $f'$ is a
    #link("note://60d115f9-9bef-47af-916a-1a60ea0b3456")[family of
    equivalences]. Since $x$ was arbitrary, $f'$ is an embedding.
]

```agda
isEmbedding→homotopy→isEmbedding :
  {i j : Level} {A : Type i} {B : Type j}
  {f f' : A → B} →
  IsEmbedding f → f ∼ f' → IsEmbedding f'
isEmbedding→homotopy→isEmbedding {_} {_} {A} {B} {f} {f'} p H x =
  totalIsContractible→characterize-＝ s x (λ y → pathAction f')
  where
  h : Σ A (λ y → f x ＝ f y) → Σ A (λ y → f' x ＝ f' y)
  h = fiber⁻¹ f' x ∘
      transport (λ ?y → Fiber f' ?y) (H x) ∘
      fiber∼⁻¹ H (f x) ∘
      fiber⁻¹' f x

  q : IsEquivalence h
  q = isEquivalenceCompose
        (fiber⁻¹ f' x)
        (transport (λ ?y → Fiber f' ?y) (H x) ∘
         fiber∼⁻¹ H (f x) ∘
         fiber⁻¹' f x)
        (fiber⁻¹-isEquivalence f' x)
        (isEquivalenceCompose
          (transport (λ ?y → Fiber f' ?y) (H x))
          (fiber∼⁻¹ H (f x) ∘ fiber⁻¹' f x)
          (transportIsEquivalence $ H x)
          (isEquivalenceCompose
            (fiber∼⁻¹ H (f x))
            (fiber⁻¹' f x)
            (fiber∼⁻¹-isEquivalence H (f x))
            (fiber⁻¹'-isEquivalence f x)))

  r : IsContractible $ Σ A (λ y → f x ＝ f y)
  r = characterize-＝→totalIsContractible x (λ y → pathAction f) (p x)

  s : IsContractible (Σ A (λ z → f' x ＝ f' z))
  s = isEquivalence→isContractible→isContractible₁ h q r

homotopy→isEmbedding↔isEmbeddeding :
  {i j : Level} {A : Type i} {B : Type j}
  {f f' : A → B} →
  f ∼ f' → (IsEmbedding f ↔ IsEmbedding f')
homotopy→isEmbedding↔isEmbeddeding {_} {_} {A} {B} {f} {f'} H =
  pair (λ p → isEmbedding→homotopy→isEmbedding p H)
       (λ p → isEmbedding→homotopy→isEmbedding p (H ⁻¹))
```

= Embeddings compose <note:d6dea5c8-f33b-446a-8dea-d4c10b35f39c>
 
#lemma(label: "75")[
    If $f ofType A -> B$ is an
    #link("note://cce94748-d9b3-4795-a3d8-c698b6dff9dd")[embedding] and $g
    ofType B -> C$ is an embedding then the
    #link("note://bc9568f6-830b-4b4e-9aab-1808b1127cb0")[composition] $g compose
    f$ is an embedding.
]
#proof[
]

```agda
isEmbeddingCompose :
  {i j k : Level} {A : Type i} {B : Type j} {C : Type k}
  (g : B → C) (f : A → B) →
  IsEmbedding g → IsEmbedding f → IsEmbedding $ g ∘ f
isEmbeddingCompose g f p q x y =
  s
  where
  r : IsEquivalence (pathAction g ∘ pathAction f)
  r = isEquivalenceCompose
        (pathAction g)
        (pathAction f)
        (p (f x) (f y))
        (q x y)

  s : IsEquivalence (pathAction (g ∘ f))
  s = isEquivalence→homotopy→isEquivalence r (pathAction-∘ f g)
```

= Commutative triangle with embedding lemma <note:8f5a36cb-8a7a-4000-9e80-239822db1379>
 
#lemma(supplement: cite_link(<rijke2025>, "Rijke 2025, exer. 11.4(a)"))[
    Consider a commuting triangle
    #figure(
        diagram($
            A edge("rr", h, ->) edge("dr", f, ->, label-side: #right) & & B edge("dl", g, ->, label-side: #left) \
                & X
        $)
    )
    with $H ofType f ~ g compose h$. If $g ofType B -> X$ is an
    #link("note://cce94748-d9b3-4795-a3d8-c698b6dff9dd")[embedding] then $f
    ofType A -> X$ is an embedding if and only if $h ofType A -> B$ is an
    embedding.
]
#proof[
    ($==>$) Assume that $f$ is an embedding. We must show that $h$ is an
    embedding. #link("note://cce94748-d9b3-4795-a3d8-c698b6dff9dd")[By
    definition], we need to show that for all $x, y ofType A$, the
    #link("note://7caf7ee0-9e2a-4761-bee9-25cd52820039")[action on paths] of $h$
    $
        ap_(h) ofType x = y -> h(x) = h(y)
    $
    is an #link("note://32c2ca55-63ba-411b-9052-676a51fd16a1")[equivalence].

    Fix $x, y ofType A$. Consider the commuting triangle of path actions
    #let app = math.sans("ap")
    #figure(
        diagram($
            x = y edge("rr", app_h, ->) edge("dr", app_(g compose h), ->, label-side: #right) & & h(x) = h(y) edge("dl", app_g, ->, label-side: #left) \
                & g(h(x)) = g(h(y))
        $)
    )
    The commutivity is given by
    #link("note://cc4b4cb3-7590-42ae-b468-1a590c448d79")[Lemma 73], which shows
    that the action on paths respects
    #link("note://bc9568f6-830b-4b4e-9aab-1808b1127cb0")[function composition].

    Since $f$ is an embedding and $H ofType f ~ g compose h$, it follows from
    the homotopy-invariance of embeddings
    (#link("note://577d40af-e9a0-4e3e-891e-003b1fdc88ff")[Lemma 74]) that $ap_(g
    compose h)$ is an equivalence. Since $g$ is an embedding, $ap_g$ is an
    equivalence.

    Therefore, in the commuting triangle above, the left and right maps are
    equivalences. By the
    #link("note://eb0e793e-d04a-4145-ad54-152aa50d2aee")[3-for-2 property for
    equivalences], it follows that the top map $ap_h$ is also an equivalence.

    Since $x, y$ were arbitrary, $h$ is an embedding.

    ($<==$) Now assume that $h$ is an embedding. Since $g$ is an embedding,
    their composite $g compose h$ is an embedding by
    #link("note://d6dea5c8-f33b-446a-8dea-d4c10b35f39c")[Lemma 75]. Embeddings
    are preserved under homotopy
    (#link("note://577d40af-e9a0-4e3e-891e-003b1fdc88ff")[Lemma 74]) and we have
    $H ofType f ~ g compose h$, so it follows that $f$ is an embedding.
]

This is an analogue of
#link("note://92588128-5591-45a6-9559-c75e846fde57")[Lemma 72], which works with
#link("note://cce94748-d9b3-4795-a3d8-c698b6dff9dd")[embeddings] instead of
#link("note://32c2ca55-63ba-411b-9052-676a51fd16a1")[retractions].

```agda
isEmbeddingRight→left→top :
  {i j k : Level} {A : Type i} {B : Type j} {X : Type k}
  (f : A → X) (g : B → X) (h : A → B) →
  f ∼ g ∘ h → IsEmbedding g → IsEmbedding f → IsEmbedding h
isEmbeddingRight→left→top f g h H p q x y =
  isEquivalenceLeft→right→top
    (pathAction $ g ∘ h) (pathAction g) (pathAction h)
    (K ⁻¹) r s
  where
  K : pathAction g ∘ pathAction h {x = x} {y = y} ∼ pathAction (g ∘ h)
  K = pathAction-∘ h g

  r : IsEquivalence $ pathAction (g ∘ h) {x = x} {y = y}
  r = isEmbedding→homotopy→isEmbedding q H x y

  s : IsEquivalence $ pathAction g {x = h x} {y = h y}
  s = p (h x) (h y)

isEmbeddingRight→top→left :
  {i j k : Level} {A : Type i} {B : Type j} {X : Type k}
  (f : A → X) (g : B → X) (h : A → B) →
  f ∼ g ∘ h → IsEmbedding g → IsEmbedding h → IsEmbedding f
isEmbeddingRight→top→left f g h H p q =
  isEmbedding→homotopy→isEmbedding (isEmbeddingCompose g h p q) (H ⁻¹)

isEmbeddingRight→left↔top :
  {i j k : Level} {A : Type i} {B : Type j} {X : Type k}
  (f : A → X) (g : B → X) (h : A → B) →
  f ∼ g ∘ h → IsEmbedding g → IsEmbedding f ↔ IsEmbedding h
isEmbeddingRight→left↔top f g h H p =
  pair (isEmbeddingRight→left→top f g h H p)
       (isEmbeddingRight→top→left f g h H p)
```

= Commuting triangle with equivalence and embedding lemma <note:dfc4bd6c-b223-4363-ab91-3faf13a7f181>
 
#lemma(supplement: cite_link(<rijke2025>, "Rijke 2025, exer. 11.4(b)"))[
    Consider a commuting triangle
    #figure(
        diagram($
            A edge("rr", h, ->) edge("dr", f, ->, label-side: #right) & & B edge("dl", g, ->, label-side: #left) \
                & X
        $)
    )
    with $H ofType f ~ g compose h$. If $h ofType A -> B$ is an
    #link("note://32c2ca55-63ba-411b-9052-676a51fd16a1")[equivalence] then $f
    ofType A -> X$ is an
    #link("note://cce94748-d9b3-4795-a3d8-c698b6dff9dd")[embedding] if and only
    if $g ofType B -> X$ is an embedding.
]
#proof[
    Since $h$ is an equivalence, by
    #link("note://731be08a-a2ad-477a-8c08-d9f26c32de41")[Lemma 3] it admits an
    #link("note://32c2ca55-63ba-411b-9052-676a51fd16a1")[inverse] $h' ofType B
    -> A$ with #link("note://3cb1b8ca-2a77-4c8a-b726-ed8f10dfd208")[homotopies]
    $
        h' compose h ~ id_(A), quad h compose h' ~ id_(B).
    $

    ($==>$) Suppose $f$ is an embedding. By
    #link("note://b92b0253-66cd-46ff-aaab-8c33541cfd45")[Lemma 48], there is a
    homotopy
    $
        g ~ f compose h'.
    $
    Since $h'$ is an equivalence, it is in particular an embedding by
    #link("note://577a5656-7132-434f-ba99-a2736940d780")[Lemma 76]. By
    assumption, $f$ is also an embedding, so their composite $f compose h'$ is
    an embedding by #link("note://d6dea5c8-f33b-446a-8dea-d4c10b35f39c")[Lemma
    75]. Finally, since $g$ is homotopic to $f ∘ h'$, and embeddings are
    invariant under homotopy
    (#link("note://577d40af-e9a0-4e3e-891e-003b1fdc88ff")[Lemma 74]), it follows
    that $g$ is an embedding.

    ($<==$) Conversely, suppose $g$ is an embedding. Because equivalences are
    embeddings (#link("note://577a5656-7132-434f-ba99-a2736940d780")[Lemma 76]),
    $h$ is an embedding. Since embeddings are closed under composition, $g
    compose h$ is an embedding. We have $f ~ g compose h$ by assumption, so it
    follows by #link("note://577d40af-e9a0-4e3e-891e-003b1fdc88ff")[Lemma 74]
    that $f$ is also an embedding.
]

```agda
isEquivalenceTop→isEmbeddingRight→IsEmbeddingLeft :
  {i j k : Level} {A : Type i} {B : Type j} {X : Type k}
  (f : A → X) (g : B → X) (h : A → B) →
  f ∼ g ∘ h → IsEquivalence h → IsEmbedding g → IsEmbedding f
isEquivalenceTop→isEmbeddingRight→IsEmbeddingLeft f g h H p q =
  s
  where
  r : IsEmbedding h
  r = isEquivalence→isEmbedding p

  s : IsEmbedding f
  s = isEmbeddingRight→top→left f g h H q r

isEquivalenceTop→isEmbeddingLeft→IsEmbeddingRight :
  {i j k : Level} {A : Type i} {B : Type j} {X : Type k}
  (f : A → X) (g : B → X) (h : A → B) →
  f ∼ g ∘ h → IsEquivalence h → IsEmbedding f → IsEmbedding g
isEquivalenceTop→isEmbeddingLeft→IsEmbeddingRight
  {_} {_} {_} {A} {B} {X} f g h H p q with isEquivalence→hasInverse p
... | (pair h' (pair K L)) = s
  where
  M : g ∼ f ∘ h'
  M = sectionTriangle f g h h' H L

  r : IsEquivalence h'
  r = inverse→isEquivalence h' h (pair L K)

  s : IsEmbedding g
  s = isEmbedding→homotopy→isEmbedding
      (isEmbeddingCompose f h' q $ isEquivalence→isEmbedding r)
        (M ⁻¹)

isEquivalenceTop→isEmbeddingLeft↔IsEmbeddingRight :
  {i j k : Level} {A : Type i} {B : Type j} {X : Type k}
  (f : A → X) (g : B → X) (h : A → B) →
  f ∼ g ∘ h → IsEquivalence h → (IsEmbedding f ↔ IsEmbedding g)
isEquivalenceTop→isEmbeddingLeft↔IsEmbeddingRight f g h H p =
  pair (isEquivalenceTop→isEmbeddingLeft→IsEmbeddingRight f g h H p)
       (isEquivalenceTop→isEmbeddingRight→IsEmbeddingLeft f g h H p)
```

= If the composition of two embeddings is an equivalence then both embeddings are equivalences <note:5d8f73d1-0578-4152-82cf-7b993aa4225a>
 
#lemma(supplement: cite_link(<rijke2025>, "Rijke 2025, exer. 11.5"))[
    Let $f ofType A arrow.hook.r B$ and $g ofType B arrow.hook.r C$ be
    #link("note://cce94748-d9b3-4795-a3d8-c698b6dff9dd")[embeddings]. If the
    #link("note://bc9568f6-830b-4b4e-9aab-1808b1127cb0")[composite] $g compose
    f$ is an #link("note://32c2ca55-63ba-411b-9052-676a51fd16a1")[equivalence],
    then both $f$ and $g$ are equivalences.
]
#proof[
    We first show that $f$ is an equivalence by comparing its
    #link("note://96d1fb9a-fd38-48cc-886f-7643637ac1e7")[fibers] with those of
    $g compose f$.

    Fix $y ofType B$. The
    #link("note://7caf7ee0-9e2a-4761-bee9-25cd52820039")[action of $g$ on paths]
    induces a #link("note://6561eded-451d-46bb-8194-c64a0acf904e")[map on total
    spaces]
    $
        Fiber_(f)(y) dot(eq) sigmaType(x, A) f(x) = y -> sigmaType(x, A) g(f(x)) = g(y) dot(eq) Fiber_(g compose f)(g(y)).
    $

    Because $g$ is an
    #link("note://cce94748-d9b3-4795-a3d8-c698b6dff9dd")[embedding], for each $x
    ofType A$, the action of $g$ on paths
    $
        ap_g ofType f(x) = y -> g(f(x)) = g(y)
    $
    is an equivalence. By
    #link("note://1e59ed56-2044-4945-8e7e-c97df7680b26")[Lemma 45], it follows
    that the induced map on total spaces is an equivalence.

    Since $g compose f$ is an equivalence, its fiber over $g(y)$ is
    #link("note://f817901c-750e-4575-a259-d83730424ade")[contractible] by
    #link("note://984c33bd-7fb6-4432-a0de-ddc279bddc1c")[Theorem 41]. As
    equivalences preserve contractibility
    (#link("note://41aea79b-658b-464d-b9c4-0326602aa2db")[Lemma 42]), the fiber
    of $f$ over $y$ is also contractible.

    Therefore each fiber of $f$ is contractible, and hence $f$ is an
    equivalence, again by
    #link("note://984c33bd-7fb6-4432-a0de-ddc279bddc1c")[Theorem 41].

    Having shown that $f$ is an equivalence, we now conclude that $g$ is an
    equivalence. Indeed, in the commutative triangle
    #figure(
        diagram($
            A edge("rr", f, ->) edge("dr", g compose f, ->, label-side: #right) & & B edge("dl", g, ->, label-side: #left) \
                & C
        $)
    )
    both the top map $f$ and left map $g compose f$ are equivalences. By the
    #link("note://eb0e793e-d04a-4145-ad54-152aa50d2aee")[3-for-2 property for
    equivalences], it follows that the right map $g$ is an equivalence as well.
]

```agda
isEmbedding→∘-isEquivalence→isEquivalence₁ :
  {i j k : Level} {A : Type i} {B : Type j} {C : Type k}
  (g : B → C) (f : A → B) →
  IsEmbedding g → IsEmbedding f →
  IsEquivalence (g ∘ f) →
  IsEquivalence f
isEmbedding→∘-isEquivalence→isEquivalence₁
  {_} {_} {_} {A} {B} {C} g f p q r = isContractibleFunction→isEquivalence s
  where
  s : (y : B) → IsContractible $ Fiber f y
  s y = w
    where
    φ : (x : A) → f x ＝ y → g (f x) ＝ g y
    φ x = pathAction g

    t : (x : A) → IsEquivalence $ φ x
    t x = p (f x) y

    u : IsEquivalence $ total φ
    u = familyOfEquivalences→totalIsEquivalence φ t

    v : IsContractible $ Σ A (λ x → g (f x) ＝ g y)
    v = isEquivalence→isContractibleFunction r (g y)

    w : IsContractible $ Σ A (λ x → f x ＝ y)
    w = isEquivalence→isContractible→isContractible₂ (total φ) u v

isEmbedding→∘-isEquivalence→isEquivalence₂ :
  {i j k : Level} {A : Type i} {B : Type j} {C : Type k}
  (g : B → C) (f : A → B) →
  IsEmbedding g → IsEmbedding f →
  IsEquivalence (g ∘ f) →
  IsEquivalence g
isEmbedding→∘-isEquivalence→isEquivalence₂ {_} {_} {_} {A} {B} {C} g f p q r =
  t
  where
  s : IsEquivalence f
  s = isEmbedding→∘-isEquivalence→isEquivalence₁ g f p q r

  t : IsEquivalence g
  t = isEquivalenceTop→left→right (g ∘ f) g f (reflexiveHomotopy (g ∘ f)) s r
```
