#import("../../../../../../library/template.typ"): *

#show: template

```agda
module Data.Sigma.Properties.Truncation where

open import Base.Function.Core
open import Base.Function.Definitions hiding (_⁻¹; _∙_)
open import Base.Function.Properties.Contractible
open import Base.Function.Properties.Equivalence
open import Base.Identity.Core
open import Base.Identity.Definitions
open import Base.Identity.Properties
open import Base.Truncation.Definitions
open import Base.Universe.Core
open import Data.Sigma.Core
open import Data.Sigma.Definitions
open import Data.Sigma.Properties.Equivalence
open import Data.Sigma.Properties.Identity
```

= Cartesian product contractible if and only if both components are contractible <note:61774716-8c8a-4461-a44f-63d9eb7c0244>
 
#lemma(
    label: "59",
    supplement: cite_link(<rijke2025>, "Rijke 2025, exer. 10.5")
)[
    For all types $A$ and $B$, the
    #link("note://23a01b78-e433-4a66-8915-bfda82ee149a")[product] $A times B$ is
    #link("note://f817901c-750e-4575-a259-d83730424ade")[contractible] if and
    only if both $A$ and $B$ are contractible.
]
#proof[
    ($==>$) Suppose $A times B$ is contractible, with
    #link("note://f817901c-750e-4575-a259-d83730424ade")[center of contraction]
    $(c, d)$ and
    #link("note://f817901c-750e-4575-a259-d83730424ade")[contraction] $C$. We
    show that both $A$ and $B$ are contractible.

    To show that $A$ is contractible, take $c$ as the center of contraction. Fix
    $x ofType A$. Applying $C$ to the pair $(x, d)$ yields a
    #link("note://261490cb-2887-4247-9a83-7f674e3c9651")[path]
    $
        (c, d) = (x, d).
    $
    Projecting to the first component using the
    #link("note://dbc89e73-b38a-49b8-b20e-06a10e62393b")[characterization of the
    identity types of products], we obtain a path $c = x$, as required.

    The contractibility of $B$ follows by symmetry: since $A times B tilde.eq B
    times A$ (#link("note://9327c53c-1b28-4d36-89cf-d7d51a91d705")[Lemma 53])
    and contracibility is preserved by
    #link("note://32c2ca55-63ba-411b-9052-676a51fd16a1")[equivalences]
    (#link("note://41aea79b-658b-464d-b9c4-0326602aa2db")[Lemma 42]), it follows
    that $B times A$ is contractible, and applying the preceding argument to $B
    times A$ shows that $B$ is contractible.

    ($<==$) Conversely, suppose $A$ and $B$ are contractible, with centers $c
    ofType A$ and $d ofType B$ and contractions $C$ and $D$, respectively. We
    show that $A times B$ is contractible. Take $(c, d)$ as the center of
    contraction. For any $(x, y) ofType A times B$, the contractions $C$ and $D$
    yield paths
    $
        c = x quad "and" quad d = y.
    $
    By the characterization of the identity types of products, these determine a
    path $(c, d) = (x, y)$.

]

```agda
×-isContractible→isContractible₁ :
  {i j : Level} {A : Type i} {B : Type j} →
  IsContractible (A × B) → IsContractible A
×-isContractible→isContractible₁ {A = A} (pair (pair c d) C) = pair c C'
  where
  C' : (x : A) → c ＝ x
  C' x = project₁ $ ＝→Equal-× $ C (pair x d)

×-isContractible→isContractible₂ :
  {i j : Level} {A : Type i} {B : Type j} →
  IsContractible (A × B) → IsContractible B
×-isContractible→isContractible₂ {A = A} {B = B} =
  ×-isContractible→isContractible₁ {A = B} {B = A} ∘
  isEquivalence→isContractible→isContractible₁ swap swapIsEquivalence

isContractible→×-isContractible :
  {i j : Level} {A : Type i} {B : Type j} →
  IsContractible A → IsContractible B → IsContractible (A × B)
isContractible→×-isContractible {A = A} {B = B} (pair c C) (pair d D) =
  pair (pair c d) E
  where
  E : (u : A × B) → pair c d ＝ u
  E (pair x y) = Equal-×→＝ $ pair (C x) (D y)

×-contractible : {i j : Level} {A : Type i} {B : Type j} →
                 IsContractible (A × B) ↔ (IsContractible A × IsContractible B)
×-contractible {_} {_} {A} {B} = pair
  (map ×-isContractible→isContractible₁ ×-isContractible→isContractible₂ ∘
   (λ u → pair u u))
  (uncurry isContractible→×-isContractible)
```

= Total space over a contractible base space is equivalent to fiber over the center of contraction <note:9f820c12-c050-423b-ae07-cc1fb0cddd37>

#lemma(
    label: "68",
    supplement: cite_link(<rijke2025>, "Rijke 2025, exer. 10.6")
)[
    Let $B$ be a #link("note://b05d0e2e-b6ab-45ab-9277-9559f4ee5e1f")[type
    family] over a type $A$. If $A$ is
    #link("note://f817901c-750e-4575-a259-d83730424ade")[contractible] with
    #link("note://f817901c-750e-4575-a259-d83730424ade")[center of contraction]
    $a ofType A$, then the map
    $
        lambda y . (a, y) ofType B(a) -> sigmaType(x, A) B(x)
    $
    is an #link("note://32c2ca55-63ba-411b-9052-676a51fd16a1")[equivalence].
]
#proof[
    Let $A$ be a
    #link("note://f817901c-750e-4575-a259-d83730424ade")[contractible type] with
    #link("note://f817901c-750e-4575-a259-d83730424ade")[center of contraction]
    $a ofType A$ and
    #link("note://f817901c-750e-4575-a259-d83730424ade")[contraction] $C$. We
    may assume without loss of generality that there is a path $C(a)^(-1) =
    refl_(a)$. Indeed, given any contraction $C$, we can always define a new
    contraction
    $
        C'(x) := C(a)^(-1) dot.op C(x)
    $
    which satisfies this requirement by the
    #link("note://ac149ae0-bd8c-4206-a7bf-eb6e7fa1575e")[left inverse law for
    paths] and the
    #link("note://95e3c813-ae44-4341-ac56-286cda078568")[definition of the
    inverse operation].

    Define a map $g ofType sigmaType(x, A) B(x) -> B(a)$ by
    $
        g(x, y) := tr_(B)(C(x)^(-1), y)
    $
    (see #link("note://1229c654-047b-4517-9f4c-df4c03224d02")[Transport along a
    path]). We show that $g$ is an
    #link("note://32c2ca55-63ba-411b-9052-676a51fd16a1")[inverse] of $f :=
    lambda y . (a, y) ofType B(a) -> sigmaType(x, A) B(x)$ by constructing
    #link("note://3cb1b8ca-2a77-4c8a-b726-ed8f10dfd208")[homotopies]
    $
        G ofType & g compose f ~ id_(B(a)), \
        H ofType & f compose g ~ id_(sigmaType(x, A) B(x)).
    $

    For the first homotopy $G$, let $y ofType B(a)$. Then
    $
        g(f(y)) dot(eq) tr_(B)(C(a)^(-1), y).
    $
    Since $C(a)^(-1) = refl_(a)$ by assumption,
    #link("note://1229c654-047b-4517-9f4c-df4c03224d02")[transporting along]
    $C(a)^(-1)$ is is
    #link("note://1229c654-047b-4517-9f4c-df4c03224d02")[judgementally equal] to
    the #link("note://efea6413-096d-4249-8ef0-a4de74fcee13")[identity map], and
    hence there is a path
    $
        tr_(B)(C(a)^(-1), y) = y.
    $

    For the second homotopy $H$, let $(x, y) ofType sigmaType(x, A) B(x)$. We
    must construct a path
    $
        (a, tr_(B)(C(x)^(-1), y)) = (x, y)
    $
    By the
    #link("note://a123eb52-0ec7-4d04-a780-e6761d564fd9")[characterization of
    $Sigma$ identity types], it suffices to give a pair
    $
        sigmaType(p, a = x) tr_(B)(p, tr_(B)(C(x)^(-1), y)) = y.
    $
    Applying the contraction $C$ at $x$ yields a path $p ofType a = x$. By
    #link("note://985f36e7-d07e-4742-ac8c-b7c0dfe1def8")[Lemma 37], which shows
    that transport along inverse paths is an inverse to transport along the
    original path, we obtain the second path
    $
        tr_(B)(C(x), tr_(B)(C(x)^(-1), y)) = y.
    $

    Thus $f$ admits a two sided inverse and is therefore an equivalence.
]

I had the idea to reuse the without loss of generality argument used in
#link("note://dc1d2466-8ead-40b1-9924-f60afcefe390")[Theorem 38] for this proof.

```agda
baseIsContractible→pairIsEquivalence :
  {i j : Level} {A : Type i} {B : A → Type j}
  (p : IsContractible A) → 
  let a : A
      a = project₁ p
  in IsEquivalence {B = Σ A B} (pair a)
baseIsContractible→pairIsEquivalence {_} {_} {A} {B} (pair a C) =
  baseIsContractible→pairIsEquivalence' C' p
  where
  C' : (x : A) → a ＝ x
  C' x = (C a) ⁻¹ ∙ C x

  p : (C' a) ⁻¹ ＝ reflexive
  p = pathAction _⁻¹ $ ⁻¹-inverseˡ (C a)

  baseIsContractible→pairIsEquivalence' :
    (C : (x : A) → a ＝ x)
    (p : (C a) ⁻¹ ＝ reflexive) →
    IsEquivalence {B = Σ A B} (pair a)
  baseIsContractible→pairIsEquivalence' C p =
    inverse→isEquivalence (pair a) g (pair G H)
    where
    g : Σ A B → B a
    g (pair x y) = transport B ((C x) ⁻¹) y

    G : g ∘ (pair a) ∼ identity {_} {B a}
    G y = transport (λ ?p → transport B ?p y ＝ y) (p ⁻¹) reflexive

    H : (pair a) ∘ g ∼ identity {_} {Σ A B}
    H (pair x y) =
      Equal→＝ (pair (C x) ((project₂ $ transportInverse (C x)) y))

baseIsContractible⇒fiber≃total :
  {i j : Level} {A : Type i} {B : A → Type j}
  (p : IsContractible A) →
  B (project₁ p) ≃ Σ A B
baseIsContractible⇒fiber≃total p =
  pair (pair $ project₁ p) (baseIsContractible→pairIsEquivalence p)
```

= The first projection is an equivalence if and only if each fiber is contractible <note:72048b5c-50ba-4b43-8c3a-18c417347534>
 
#lemma(
    label: "43",
    supplement: cite_link(<rijke2025>, "Rijke 2025, exer. 10.7(b)")
)[
    Let $B$ be a #link("note://b05d0e2e-b6ab-45ab-9277-9559f4ee5e1f")[type
    family] over a type $A$. The
    #link("note://ae098784-7572-4d29-b548-a2db9b6d004a")[first projection]
    $
        project1 ofType sigmaType(x, A) B(x) -> A
    $
    is an #link("note://32c2ca55-63ba-411b-9052-676a51fd16a1")[equivalence] if
    and only if the #link("note://85839d30-6530-4e54-a8ba-efd1c8709928")[fiber]
    $B(x)$ is #link("note://f817901c-750e-4575-a259-d83730424ade")[contractible]
    for each $x ofType A$.
]
#proof[
    By #link("note://984c33bd-7fb6-4432-a0de-ddc279bddc1c")[Theorem 41], a map
    is an equivalence if and only if each of its
    #link("note://96d1fb9a-fd38-48cc-886f-7643637ac1e7")[fibers] is
    contractible. Fix $x ofType A$. By
    #link("note://f9a042a9-e79b-4277-8d9b-e440679252d5")[Lemma 39], there is an
    equivalence
    $
        Fiber_(project1)(x) tilde.eq B(x),
    $
    identifying the #link("note://96d1fb9a-fd38-48cc-886f-7643637ac1e7")[fiber]
    of the first projection over $x$ with the type family
    #link("note://85839d30-6530-4e54-a8ba-efd1c8709928")[fiber] $B(x)$.

    Since contractibility is preserved under equivalence by
    #link("note://41aea79b-658b-464d-b9c4-0326602aa2db")[Lemma 42], the fiber
    $Fiber_(project1)(x)$ is contractible if and only if $B(x)$ is
    contractible. The claim follows.
]

```agda
project₁-isEquivalence↔fibersContractible :
  {i j : Level} {A : Type i} {B : A → Type j} →
  IsEquivalence (project₁ {A = A} {B = B}) ↔ ((x : A) → IsContractible (B x))
project₁-isEquivalence↔fibersContractible {_} {_} {A} {B} = q ∘↔ p
  where
  p : IsEquivalence project₁ ↔
      IsContractibleFunction (project₁ {A = A} {B = B})
  p = isEquivalence↔isContractibleFunction

  q : ((x : A) → IsContractible (Fiber project₁ x)) ↔
      ((x : A) → IsContractible (B x))
  q = Π↔swap
    (λ x → isEquivalence→isContractible↔isContractible
      (fiberProject₁→fiber x) (fiberProject₁→fiberEquivalence x))
```

= Lift to total space via dependent function is an equivalence if and only if fibers of type family are contractible <note:0e491737-f1c7-4712-bf2c-5bbf45cbd155>

#lemma(supplement: cite_link(<rijke2025>, "Rijke 2025, exer. 10.7(c)"))[
    Let $B$ be a #link("note://b05d0e2e-b6ab-45ab-9277-9559f4ee5e1f")[type
    family] over a type $A$ and let $f ofType piType(x, A) B(x)$ be a dependent
    function. Then the map
    $
        s := lambda x . (x, f(x)) ofType A -> sigmaType(x, A) B(x)
    $
    is an #link("note://32c2ca55-63ba-411b-9052-676a51fd16a1")[equivalence] if
    and only if the #link("note://85839d30-6530-4e54-a8ba-efd1c8709928")[fiber]
    $B(x)$ is #link("note://f817901c-750e-4575-a259-d83730424ade")[contractible]
    for each $x ofType A$.
]
#proof[
    We instead show that $s$ is an equivalence if and only if the
    #link("note://ae098784-7572-4d29-b548-a2db9b6d004a")[first projection]
    $project1 ofType sigmaType(x, A) B(x) -> A$ is an equivalence. The claim
    then follows by #link("note://72048b5c-50ba-4b43-8c3a-18c417347534")[Lemma
    43], which shows that $project1$ is an equivalence if and only if the fiber
    $B(x)$ is contractible for each $x ofType A$.

    ($==>$) Suppose $s$ is an equivalence. Then by
    #link("note://731be08a-a2ad-477a-8c08-d9f26c32de41")[Lemma 3], it admits an
    #link("note://32c2ca55-63ba-411b-9052-676a51fd16a1")[inverse] $g ofType
    sigmaType(x, A) B(x) -> A$ with
    #link("note://3cb1b8ca-2a77-4c8a-b726-ed8f10dfd208")[homotopies]
    $
        G ofType g compose s ~ id_(A) quad "and" quad
        H ofType s compose g ~ id_(sigmaType(x, A) B(x)).
    $

    Evaluating the second homotopy $H$ at an arbitrary $(x, y) ofType
    sigmaType(x, A) B(x)$ yields a path
    $
        (g((x, y)), f(g((x, y)))) = (x, y).
    $
    Using the first projection of the
    #link("note://a123eb52-0ec7-4d04-a780-e6761d564fd9")[characterization of
    $Sigma$ identity types], we obtain a path
    $
        g((x, y)) = x dot(eq) project1((x, y)).
    $
    Since $(x, y)$ was arbitrary, this defines a homotopy $g ~ project1$. By
    #link("note://52746242-840c-49cd-b924-5d5889004220")[Lemma 25], inverses are
    invariant under homotopy, so $project1$ is also an inverse of $s$, and hence
    an equivalence.

    ($<==$) Conversely, suppose $project1 ofType sigmaType(x, A) B(x) -> A$ is
    an equivalence. By
    #link("note://731be08a-a2ad-477a-8c08-d9f26c32de41")[Lemma 3], there is a
    function $g ofType A -> sigmaType(x, A) B(x)$ equipped with homotopies
    $
        G ofType g compose project1 ~ id_(sigmaType(x, A) B(x)) quad "and" quad
        H ofType project1 compose g ~ id_(A).
    $
    For each $x ofType A$, the homotopy $G$ at the pair $(x, f(x))$ gives a path
    $
        g(x) = (x, (f(x))),
    $
    so there is a homotopy $g ~ s$. By
    #link("note://52746242-840c-49cd-b924-5d5889004220")[Lemma 24], the map $s$
    is an inverse of $project1$, and therefore an equivalence.
]

```agda

pairIsEquivalence→project₁-isEquivalence :
  {i j : Level} {A : Type i} {B : A → Type j}
  (f : (x : A) → B x) →
  IsEquivalence (λ x → pair x (f x)) → IsEquivalence (project₁ {A = A} {B = B})
pairIsEquivalence→project₁-isEquivalence {A = A} {B = B} f p with
  isEquivalence→hasInverse p
... | (pair g p'@(pair G H)) =
  inverse→isEquivalence
    project₁ s
    (inverseInverse (λ x → pair x (f x)) project₁ q)
  where
  s : A → Σ A B
  s = λ x → pair x (f x)

  K : g ∼ project₁
  K (pair x y) = project₁ $ ＝→Equal $ H (pair x y)

  q : Inverse s project₁
  q = inverse→homotopy→inverseʳ p' K

project₁-isEquivalence→pairIsEquivalence :
  {i j : Level} {A : Type i} {B : A → Type j}
  (f : (x : A) → B x) →
  IsEquivalence (project₁ {A = A} {B = B}) → IsEquivalence (λ x → pair x (f x))
project₁-isEquivalence→pairIsEquivalence {A = A} {B = B} f p with
  isEquivalence→hasInverse p
... | (pair g p'@(pair G H)) = 
  inverse→isEquivalence
    s project₁
    (inverseInverse project₁ s q)
  where
  s = (λ x → pair x (f x))

  K : g ∼ s
  K x = G (pair x (f x))

  q : Inverse project₁ s
  q = inverse→homotopy→inverseʳ p' K

pairIsEquivalence↔project₁-isEquivalence :
  {i j : Level} {A : Type i} {B : A → Type j}
  (f : (x : A) → B x) →
  IsEquivalence (λ x → pair x (f x)) ↔ IsEquivalence (project₁ {A = A} {B = B})
pairIsEquivalence↔project₁-isEquivalence f =
  pair (pairIsEquivalence→project₁-isEquivalence f)
       (project₁-isEquivalence→pairIsEquivalence f)

pairIsEquivalence↔fibersContractible :
  {i j : Level} {A : Type i} {B : A → Type j}
  (f : (x : A) → B x) →
  IsEquivalence (λ x → pair x (f x)) ↔ ((x : A) → IsContractible (B x))
pairIsEquivalence↔fibersContractible {A = A} {B = B} f = q ∘↔ p
  where
  p : IsEquivalence (λ x → pair x (f x)) ↔ IsEquivalence project₁
  p = pairIsEquivalence↔project₁-isEquivalence f

  q : IsEquivalence project₁ ↔ ((x : A) → IsContractible (B x))
  q = project₁-isEquivalence↔fibersContractible
```
