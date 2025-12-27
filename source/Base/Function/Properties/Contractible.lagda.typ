#import("../../../../../../library/template.typ"): *

#show: template

```agda
module Base.Function.Properties.Contractible where

open import Base.Function.Core
open import Base.Function.Definitions
open import Base.Function.FiberIdentity as Fiber
open import Base.Function.Properties.Equivalence
open import Base.Function.Properties.Homotopy
open import Base.Identity.Core
open import Base.Identity.Definitions as Identity
open import Base.Identity.Properties as Identity
open import Base.Identity.Syntax
open import Base.Truncation.Definitions
open import Base.Universe.Core
open import Data.Sigma.Core
open import Data.Unit.Core
```

= Every contractible map is an equivalence <note:e6848e01-6f0e-415e-9010-b0f2e2b28370>
 
#theorem(
    label: "32",
    supplement: cite_link(<rijke2025>, "thm. 10.3.5")
)[
    Every #link("note://ce3caacd-6477-4d21-b37e-c5423974464a")[contractible map]
    is an #link("note://32c2ca55-63ba-411b-9052-676a51fd16a1")[equivalence].
]
#proof[
    Let $f ofType A -> B$ be a
    #link("note://ce3caacd-6477-4d21-b37e-c5423974464a")[contractible map]. We
    construct an inverse map $g ofType B -> A$ and show that it is both a
    #link("note://32c2ca55-63ba-411b-9052-676a51fd16a1")[section] and a
    #link("note://32c2ca55-63ba-411b-9052-676a51fd16a1")[retraction] of $f$.

    For $y ofType B$, the
    #link("note://96d1fb9a-fd38-48cc-886f-7643637ac1e7")[fiber] $Fiber_(f)(y)
    dot(eq) sigmaType(x, A) f(x) = y$ is
    #link("note://f817901c-750e-4575-a259-d83730424ade")[contractible by
    assumption]. Let $(x, p)$ be its
    #link("note://f817901c-750e-4575-a259-d83730424ade")[center of
    contraction]. Define $g(y) := x$. Using the
    #link("note://261490cb-2887-4247-9a83-7f674e3c9651")[path] $p$ for each $y
    ofType B$ then gives a
    #link("note://3cb1b8ca-2a77-4c8a-b726-ed8f10dfd208")[homotopy]
    $
        f compose g ~ id_(B),
    $
    so $g$ is a section of $f$.

    It remains to that $g$ is a retraction of $f$ by constructing a homotopy $g
    compose f ~ id_(A)$. Applying the contractibility of the fiber over $f(x)$,
    we obtain a #link("note://f817901c-750e-4575-a259-d83730424ade")[center of
    contraction]
    $
        (c, p) ofType sigmaType(c', A) f(c') = f(x)
    $
    together with a
    #link("note://f817901c-750e-4575-a259-d83730424ade")[contraction]
    $
        C ofType piType(u, sigmaType(c', A) f(c') = f(x)) (c, p) = u.
    $
    By definition of $g$, we have $g(f(x)) dot(eq) c$, so our goal is to
    construct a path $c = x$.

    The pair $(x, refl_(f(x)))$ is an element of the fiber over $f(x)$, so
    applying the contraction $C$ yields an identification
    $
        (c, p) = (x, refl_(f(x))).
    $
    By the characterization of fiber identity types
    (#link("note://571b0e34-86b8-4d44-9e85-d862dafc62e2")[Lemma 29]), this path
    corresponds #link("note://4778d3fd-56f0-4f8f-8810-8440b89e9550")[to a pair]
    $
        sigmaType(alpha, c = x) p = ap_(f)(alpha) dot.op refl_(f(x)).
    $
    #link("note://ae098784-7572-4d29-b548-a2db9b6d004a")[Projecting] to the
    first component yields the required path $c = x$.

    Thus $g compose f ~ id_(A)$, completing the proof that $f$ is an
    #link("note://32c2ca55-63ba-411b-9052-676a51fd16a1")[equivalence].
]

```agda
isContractibleFunction→IsEquivalence :
  {i j : Level} {A : Type i} {B : Type j}
  {f : A → B} →
  IsContractibleFunction f → IsEquivalence f
isContractibleFunction→IsEquivalence {_} {_} {A} {B} {f} p =
  inverse→isEquivalence f g (pair H K)
  where
  g : B → A
  g y = project₁ $ project₁ $ p y

  H : g ∘ f ∼ identity {_} {A}
  H x with p (f x)
  ... | pair (pair c p) C = project₁ q'
    where
    q : pair c p ＝ pair x reflexive
    q = C (pair x reflexive)

    q' : Fiber.Equal (pair c p) (pair x reflexive)
    q' = ＝→Equal q

  K : f ∘ g ∼ identity {_} {B}
  K y = project₂ $ project₁ $ p y
```

= Every coherently invertible map has contractible fibers <note:9e5a2bbc-267a-4469-bc31-f5252ba2ff95>
 
#lemma(
    label: "31",
    supplement: cite_link(<rijke2025>, "Rijke 2025, prop. 10.4.2")
)[
    If a map is #link("note://3f3eff81-188f-4284-b83a-9dd41a67c297")[coherently
    invertible], then it has
    #link("note://ce3caacd-6477-4d21-b37e-c5423974464a")[contractible fibers].
]
#proof[
    Let $f ofType A -> B$ be a
    #link("note://3f3eff81-188f-4284-b83a-9dd41a67c297")[coherently invertible
    map]. Then there exists a function $g ofType B -> A$ together with
    #link("note://3cb1b8ca-2a77-4c8a-b726-ed8f10dfd208")[homotopies]
    $
        G & ofType g compose f ~ id_(A), \
        H & ofType f compose g ~ id_(B), \
        K & ofType f dot.op G ~ H dot.op f.
    $

    Fix $y ofType B$. We show that the
    #link("note://96d1fb9a-fd38-48cc-886f-7643637ac1e7")[fiber]
    $
        Fiber_(F)(y) dot(eq) sigmaType(x, A) f(x) = y
    $
    is #link("note://f817901c-750e-4575-a259-d83730424ade")[contractible]. The
    homotopy $H$ supplies a
    #link("note://261490cb-2887-4247-9a83-7f674e3c9651")[path]
    $
        H(y) ofType f(g(y)) = y
    $
    and hence an element $(g(y), H(y))$ of the fiber of $f$ over $y$, which we
    take as the #link("note://f817901c-750e-4575-a259-d83730424ade")[center of
    contraction].

    It remains to construct a contraction
    $
        piType(u, Fiber_(f)(y)) (g(y), H(y)) = u.
    $

    By #link("note://ae098784-7572-4d29-b548-a2db9b6d004a")[$Sigma$-induction],
    it suffices to show that for every $x ofType A$ and $p ofType f(x) = y$,
    there is a path
    $
        (g(y), H(y)) = (x, p).
    $
    By #link("note://261490cb-2887-4247-9a83-7f674e3c9651")[path induction] on
    $p$, we may assume $y$ is $f(x)$ and that $p$ is $refl_(f(x))$, in which
    case it suffices to construct a path
    $
        (g(f(x)), H(f(x))) = (x, refl_(f(x))).
    $
    Using the characterization of fiber identity types
    (#link("note://571b0e34-86b8-4d44-9e85-d862dafc62e2")[Lemma 29]), this path
    #link("note://4778d3fd-56f0-4f8f-8810-8440b89e9550")[corresponds to a pair]
    $
        sigmaType(alpha, g(f(x)) = x) H(f(x)) = ap_(f)(alpha) dot.op refl_(f(x)).
    $
    The homotopy $G$ provides a path $G(x) ofType g(f(x)) = x$. Moreover,
    evaluating the coherence homotopy $K$ at $x$ and taking the
    #link("note://95e3c813-ae44-4341-ac56-286cda078568")[inverse] yields
    $
        H(f(x)) = ap_(f)(G(x)),
    $
    which by the #link("note://50f1bf11-5d39-455c-a39e-0d560ac5cee5")[right unit
    law for path concatenation], gives
    $
        H(f(x)) = ap_(f)(G(x)) dot.op refl_(f(x)).
    $
    This completes the construction of the two required paths, and hence the
    contraction of the fiber of $f$ over $y$.
]

```agda
isCoherentlyInvertible→isContractibleFunction :
  {i j : Level} {A : Type i} {B : Type j}
  {f : A → B} →
  IsCoherentlyInvertible f → IsContractibleFunction f
isCoherentlyInvertible→isContractibleFunction {f = f}
  (pair g (pair (pair G H) K)) y = pair (pair (g y) (H y)) C
  where
  C : (u : Fiber f y) → pair (g y) (H y) ＝ u
  C (pair x reflexive) = Equal→＝ (pair (G x) p)
    where
    p : H (f x) ＝ pathAction f (G x) Identity.∙ reflexive
    p = H (f x)
          ＝[ (K x) Identity.⁻¹ ]
        pathAction f (G x)
          ＝[ Identity.∙-unitʳ _ Identity.⁻¹ ]
        pathAction f (G x) Identity.∙ reflexive ∎
```

= Has inverse implies coherently inveritble <note:17fc0810-3038-449d-8d32-58ea94fbb62b>
 
#lemma(
    label: "30",
    supplement: cite_link(<rijke2025>, "lem. 10.4.5")
)[
    If a map #link("note://32c2ca55-63ba-411b-9052-676a51fd16a1")[has an
    inverse] then it is
    #link("note://3f3eff81-188f-4284-b83a-9dd41a67c297")[coherently invertible].
]

I didn't write my own proof for this one. Instead, I had to follow Rijke's proof
pretty closely because I didn't know what was going on. The proof makes sense
when you get down in the weeds, but I wouldn't have come up with this on my own
without a lot more work.

TODO: Write a paper proof. Had one in the previous notes, but I have to switch
some things and I'm too lazy right now. Plus he proof just totally sucks.

```agda
hasInverse→isCoherentlyInvertible :
  {i j : Level} {A : Type i} {B : Type j}
  {f : A → B} →
  HasInverse f → IsCoherentlyInvertible f
hasInverse→isCoherentlyInvertible {_} {_} {A} {B} {f} (pair g (pair G H)) =
  pair g (pair (pair G H') K)
  where
  H' : f ∘ g ∼ identity {_} {B}
  H' y = ((H $ f $ g y) Identity.⁻¹) Identity.∙
         pathAction f (G $ g y) Identity.∙
         (H y)

  K : f ∙ₗ G ∼ H' ∙ᵣ f
  K x = β''
    where
    α : pathAction (f ∘ g ∘ f) (G x) Identity.∙ H (f x) ＝
        H (f (g (f x))) Identity.∙ pathAction f (G x)
    α = homotopyNatural {f = f ∘ g ∘ f} {g = f} (H ∙ᵣ f) (G x)
                                                            
    β : pathAction f (G x) ＝
        (H (f (g (f x)))) Identity.⁻¹ Identity.∙
           (pathAction (f ∘ g ∘ f) (G x) Identity.∙ H (f x))
    β = Identity.⁻¹∙ $ α Identity.⁻¹
                         
    β' : pathAction f (G x) ＝
         (H (f (g (f x)))) Identity.⁻¹ Identity.∙
           pathAction (f ∘ g ∘ f) (G x) Identity.∙
           H (f x)
    β' = β Identity.∙
           Identity.∙-associative _ (pathAction (f ∘ g ∘ f) (G x)) (H (f x))
           Identity.⁻¹
             
    γ : pathAction f (G (g (f x))) ＝ pathAction (f ∘ g ∘ f) (G x)
    γ = pathAction f (G (g (f x)))
        ＝[ pathAction (pathAction f) (homotopyNaturalIdentity G x) ]
           pathAction f (pathAction (g ∘ f) (G x))
             ＝[ pathAction-∘ (g ∘ f) f (G x) ]
           pathAction (f ∘ g ∘ f) (G x) ∎
                                        
    β'' : pathAction f (G x) ＝
          (H (f (g (f x)))) Identity.⁻¹ Identity.∙
            pathAction f (G (g (f x))) Identity.∙
            H (f x)
    β'' =
      transport (λ ?x → pathAction f (G x) ＝ (H (f (g (f x)))) Identity.⁻¹
                        Identity.∙ ?x Identity.∙ H (f x))
                (γ Identity.⁻¹)
                β'
```

= Every equivalence is a contractible map <note:3a8a7dd6-0578-45a4-a07b-052ce889aa1c>
 
#theorem(
    label: "33",
    supplement: cite_link(<rijke2025>, "Rijke 2025, thm. 10.4.6")
)[
    Every #link("note://32c2ca55-63ba-411b-9052-676a51fd16a1")[equivalence] is a
    #link("note://ce3caacd-6477-4d21-b37e-c5423974464a")[contractible map].
]
#proof[
    If a map is an
    #link("note://32c2ca55-63ba-411b-9052-676a51fd16a1")[equivalence], then it
    has an #link("note://32c2ca55-63ba-411b-9052-676a51fd16a1")[inverse] by
    #link("note://731be08a-a2ad-477a-8c08-d9f26c32de41")[Lemma 3]. Then it is
    #link("note://3f3eff81-188f-4284-b83a-9dd41a67c297")[coherently invertible]
    by #link("note://17fc0810-3038-449d-8d32-58ea94fbb62b")[Lemma 30], and
    #link("note://9e5a2bbc-267a-4469-bc31-f5252ba2ff95")[Lemma 31] shows that
    all coherently invertible maps have
    #link("note://f817901c-750e-4575-a259-d83730424ade")[contractible]
    #link("note://96d1fb9a-fd38-48cc-886f-7643637ac1e7")[fibers].
]

```agda
isEquivalence→isContractibleFunction :
  {i j : Level} {A : Type i} {B : Type j}
  {f : A → B} →
  IsEquivalence f → IsContractibleFunction f
isEquivalence→isContractibleFunction =
  isCoherentlyInvertible→isContractibleFunction ∘
  hasInverse→isCoherentlyInvertible ∘
  isEquivalence→hasInverse
```

= Equivalence if and only if contractible map <note:984c33bd-7fb6-4432-a0de-ddc279bddc1c>

#theorem(label: "41")[
    A map is an
    #link("note://32c2ca55-63ba-411b-9052-676a51fd16a1")[equivalence] if and
    only if it has
    #link("note://ce3caacd-6477-4d21-b37e-c5423974464a")[contractible fibers].
]
#proof[
    By Theorems #link("note://e6848e01-6f0e-415e-9010-b0f2e2b28370")[32] and
    #link("note://3a8a7dd6-0578-45a4-a07b-052ce889aa1c")[33].
]

```agda
isEquivalence↔isContractibleFunction :
  {i j : Level} {A : Type i} {B : Type j}
  {f : A → B} →
  IsEquivalence f ↔ IsContractibleFunction f
isEquivalence↔isContractibleFunction =
  pair
  isEquivalence→isContractibleFunction
  isContractibleFunction→IsEquivalence
```

= If a type is contractible than it has contractible identity types <note:1d8b9cbe-0517-4ca7-840a-d9601bedde8e>

#lemma(supplement: cite_link(<rijke2025>, "Rijke 2025, exer. 10.1"))[
    If a type $A$ is
    #link("note://f817901c-750e-4575-a259-d83730424ade")[contractible], then for
    all $x, y ofType A$, the
    #link("note://261490cb-2887-4247-9a83-7f674e3c9651")[identity type] $x
    attach(eq, br: A) y$ is also contractible.
]
#proof[
    Let $A$ be a
    #link("note://f817901c-750e-4575-a259-d83730424ade")[contractible type] with
    #link("note://f817901c-750e-4575-a259-d83730424ade")[center of contraction]
    $c ofType A$ and
    #link("note://f817901c-750e-4575-a259-d83730424ade")[contraction] $C ofType
    piType(x, A) c = x$. Fix $x, y ofType A$. We show that the
    #link("note://261490cb-2887-4247-9a83-7f674e3c9651")[identity type] $x
    attach(eq, br: A) y$ is
    #link("note://f817901c-750e-4575-a259-d83730424ade")[contractible].

    Take the #link("note://261490cb-2887-4247-9a83-7f674e3c9651")[path]
    $
        C(x)^(-1) dot.op C(y) ofType x = y.
    $
    as the center of contraction. For the contraction, let $p ofType x = y$. By
    #link("note://261490cb-2887-4247-9a83-7f674e3c9651")[path induction] on $p$,
    we may assume $y$ is $x$ and that $p$ is $refl_(x)$. In this case it
    suffices to construct a path
    $
        C(x)^(-1) dot.op C(x) = refl_(x),
    $
    which we obtain immediately from the
    #link("note://ac149ae0-bd8c-4206-a7bf-eb6e7fa1575e")[left inverse law for
    paths].
]

```agda
isContractible→＝-isContractible :
  {i : Level} {A : Type i}
  (p : IsContractible A) →
  (x y : A) → IsContractible (x ＝ y)
isContractible→＝-isContractible (pair c C) x y = pair d D
  where
  d : x ＝ y
  d = (C x) Identity.⁻¹ Identity.∙ (C y)

  D : (p : x ＝ y) → d ＝ p
  D reflexive = Identity.⁻¹-inverseˡ (C x)
```

= For all maps with a retraction, if the codomain is contractible then the domain is contractible <note:591c6be7-77c3-4215-a126-f27d87c6bd65>
 
#lemma(supplement: cite_link(<rijke2025>, "Rijke 2025, exer. 10.2"))[
    For all maps $f ofType A -> B$ with a
    #link("note://32c2ca55-63ba-411b-9052-676a51fd16a1")[retraction], if the
    codomain $B$ is
    #link("note://f817901c-750e-4575-a259-d83730424ade")[contractible] then the
    domain $A$ is contractible.
]
#proof[
    Let $g ofType B -> A$ be a retraction of $f ofType A -> B$ with
    #link("note://3cb1b8ca-2a77-4c8a-b726-ed8f10dfd208")[homotopy] $H ofType g
    compose f ~ id_(A)$. Suppose $B$ is
    #link("note://f817901c-750e-4575-a259-d83730424ade")[contractible] with
    #link("note://f817901c-750e-4575-a259-d83730424ade")[center of contraction]
    $c ofType B$ and
    #link("note://f817901c-750e-4575-a259-d83730424ade")[contraction] $C ofType
    piType(y, B) c = y$. We show that the type $A$ is contractible.

    Take $g(c) ofType A$ for the center of contraction. For the contraction, let
    $x ofType A$. The contraction $C$ gives a
    #link("note://261490cb-2887-4247-9a83-7f674e3c9651")[path] $C(x) ofType c =
    f(x)$, and applying the homotopy $H$ at $x$ yields a path $g(f(x)) =
    x$. Therefore there is a path
    $
        g(c) = g(f(x)) = x.
    $
    This completes the construction of the contraction, and hence $A$ is
    contractible.
]

Intution: Maps with retractions are injective. If a map into a singleton is
injective then there must be only one element of the domain too, since two
different elements would be forced to map to the same unique element of the
codomain.

```agda
retraction→isContractible→isContractible :
  {i j : Level} {A : Type i} {B : Type j}
  (f : A → B) (g : B → A) →
  LeftInverse f g →
  IsContractible B → IsContractible A
retraction→isContractible→isContractible {A = A} f g G (pair c C) =
  pair d D
  where
  d : A
  d = g c

  D : (x : A) → d ＝ x
  D x = pathAction g (C (f x)) Identity.∙ G x
```

= The constant function into the unit type is an equivalence if and only if the domain is contractible <note:41e67f5f-60c1-4549-8e24-160141e4bd64>

#lemma(
    label: "34",
    supplement: cite_link(<rijke2025>, "Rijke 2025, exer. 10.3(a)")
)[
    For any type $A$, the map $constant_(star) ofType A -> unitType$ is an
    #link("note://32c2ca55-63ba-411b-9052-676a51fd16a1")[equivalence] if and
    only if $A$ is
    #link("note://f817901c-750e-4575-a259-d83730424ade")[contractible].
]
#proof[
    ($==>$) If $constant_(star) ofType A -> unitType$ is an
    #link("note://32c2ca55-63ba-411b-9052-676a51fd16a1")[equivalence], then in
    particular it comes equipped with a
    #link("note://32c2ca55-63ba-411b-9052-676a51fd16a1")[retraction], that is,
    there is a function $g ofType unitType -> A$ and a
    #link("note://3cb1b8ca-2a77-4c8a-b726-ed8f10dfd208")[homotopy] $H ofType h
    compose constant_(star) ~ id_(A)$. To show that $A$ is
    #link("note://f817901c-750e-4575-a259-d83730424ade")[contractible], take
    $h(star)$ as the #link("note://f817901c-750e-4575-a259-d83730424ade")[center
    of contraction]. For the
    #link("note://f817901c-750e-4575-a259-d83730424ade")[contraction], fix $x
    ofType A$ and observe that applying the homotopy $H$ at $x$ yields $H(x)
    ofType h(star) = x$ as required.

    ($<==$) Conversely, suppose $A$ is contractible, with center of contraction
    $c ofType A$ and contraction $C ofType piType(x, A) c = x$. To show that
    $constant_(star) ofType A -> unitType$ is an equivalence, we show that
    $constant_(c) ofType unitType -> A$ is its inverse by constructing homotopies
    $
        G ofType & constant_(c) compose constant_(star) ~ id_(A), \
        H ofType & constant_(star) compose constant_(c) ~ id_(unitType).
    $

    The homotopy $H$ follows by
    #link("note://fe0ba530-46e9-4031-83bb-330db4d12b4e")[induction on the unit
    type], where $constant_(star)(constant_(c)(star)) = star$ holds
    #link("note://a0baf580-5da2-4328-bfbd-202bedf37747")[judgementally]. For
    $G$, note that for each $x ofType A$, the path
    $constant_(c)(constant_(star)(x)) = x$ evaluates to $c = x$. Therefore, we
    can take the contraction $C$ for the homotopy $G$. Hence $constant_(star)$
    is an equivalence.
]

See #link("note://11168612-1fca-405d-b3c5-2ecb0ece3521")[Constant function].

```agda
constantUnitIsEquivalence→isContractible :
  {i : Level} {A : Type i} →
  IsEquivalence (constant {A = A} ⋆) →
  IsContractible A
constantUnitIsEquivalence→isContractible {_} {A} (pair (pair g G) _) =
  pair (g ⋆) G

isContractible→constantUnitIsEquivalence :
  {i : Level} {A : Type i} →
  IsContractible A →
  IsEquivalence (constant {A = A} ⋆)
isContractible→constantUnitIsEquivalence {_} {A} (pair c C) =
  inverse→isEquivalence (constant ⋆) (constant c) (pair G H)
  where
  G : constant c ∘ constant ⋆ ∼ identity {_} {A}
  G = C

  H : constant ⋆ ∘ constant c ∼ identity {_} {𝟏}
  H ⋆ = reflexive
```

= Map between contractible types is an equivalence <note:41aea79b-658b-464d-b9c4-0326602aa2db>
 
#lemma(
    label: "42",
    supplement: cite_link(<rijke2025>, "Rijke 2025, exer. 10.3(b)")
)[
    Consider a function $f ofType A -> B$. If any two of the three statements

    1. $A$ is #link("note://f817901c-750e-4575-a259-d83730424ade")[contractible]
    2. $B$ is contractible
    3. $f$ is an
       #link("note://32c2ca55-63ba-411b-9052-676a51fd16a1")[equivalence]

    hold, then so does the third.
]
#proof[
    In each case, we can use the
    #link("note://eb0e793e-d04a-4145-ad54-152aa50d2aee")[3-for-2 property for
    equivalences] applied to the following diagram:
    #figure(
        diagram($
            A edge("rr", f, ->) edge("dr", constant_(star), ->, label-side: #right) & & B edge("dl", constant_(star), ->, label-side: #left) \
                & #math.bold($1$)
        $)
    )

    We have a #link("note://3cb1b8ca-2a77-4c8a-b726-ed8f10dfd208")[homotopy]
    $constant_(star) ~ constant_(star) compose f$ by the definition of the
    #link("note://11168612-1fca-405d-b3c5-2ecb0ece3521")[constant map], so the
    diagram commutes.

    If $A$ and $B$ are both contractible, then $constant_(star) ofType A ->
    unitType$ and $constant_(star) ofType B -> unitType$ are both equivalences
    by #link("note://41e67f5f-60c1-4549-8e24-160141e4bd64")[Lemma 34], and hence
    $f ofType A -> B$ is an equivalence by the 3-for-2 property.

    Suppose $A$ is contractible and $f ofType A -> B$ is an equivalence. By
    Lemma 34, it suffices to show $constant_(star) ofType B -> unitType$ is an
    equivalence, which follows by Lemma 34 applied to the contractibility of $A$
    and the 3-for-2 property. The argument is analogous if $B$ is contractible.
]

```agda
isContractible→isContractible→isEquivalence :
  {i j : Level} {A : Type i} {B : Type j}
  (f : A → B) →
  IsContractible A → IsContractible B → IsEquivalence f
isContractible→isContractible→isEquivalence f p q =
  isEquivalenceLeft→right→top (constant ⋆) (constant ⋆) f H
                              (isContractible→constantUnitIsEquivalence p)
                              (isContractible→constantUnitIsEquivalence q)
  where
  H : constant ⋆ ∼ constant ⋆ ∘ f
  H x = reflexive

isEquivalence→isContractible→isContractible₁ :
  {i j : Level} {A : Type i} {B : Type j}
  (f : A → B) →
  IsEquivalence f → IsContractible A → IsContractible B
isEquivalence→isContractible→isContractible₁ f p q =
  constantUnitIsEquivalence→isContractible $
    isEquivalenceTop→left→right (constant ⋆) (constant ⋆) f H p $
    isContractible→constantUnitIsEquivalence q
  where
  H : constant ⋆ ∼ constant ⋆ ∘ f
  H x = reflexive

isEquivalence→isContractible→isContractible₂ :
  {i j : Level} {A : Type i} {B : Type j}
  (f : A → B) →
  IsEquivalence f → IsContractible B → IsContractible A
isEquivalence→isContractible→isContractible₂ f p q =
  constantUnitIsEquivalence→isContractible $
    isEquivalenceTop→right→left (constant ⋆) (constant ⋆) f H p $
    isContractible→constantUnitIsEquivalence q
  where
  H : constant ⋆ ∼ constant ⋆ ∘ f
  H x = reflexive

isEquivalence→isContractible↔isContractible :
  {i j : Level} {A : Type i} {B : Type j}
  (f : A → B) →
  IsEquivalence f → IsContractible A ↔ IsContractible B
isEquivalence→isContractible↔isContractible f p =
  pair (isEquivalence→isContractible→isContractible₁ f p)
       (isEquivalence→isContractible→isContractible₂ f p)
```

= A type is contractible if and only if it is equivalent to the unit type <note:87576cff-1971-462a-a83c-221a8f2672a0>
 
#corollary[
    A type is #link("note://f817901c-750e-4575-a259-d83730424ade")[contractible]
    if and only if it is
    #link("note://32c2ca55-63ba-411b-9052-676a51fd16a1")[equivalent] to the unit
    type.
]
#proof[
    ($==>$) If $A$ is contractible, then $constant_(star) ofType A -> unitType$
    is an equivalence by
    #link("note://41e67f5f-60c1-4549-8e24-160141e4bd64")[Lemma 34].

    ($<==$) Conversely, suppose $f ofType A -> unitType$ is an equivalence. By
    #link("note://cabe5b8c-706f-4aca-b786-ac23e95a5d51")[Lemma 35], there is a
    homotopy $f ~ constant_(star)$. It follows by
    #link("note://4b08592f-f5db-4f89-a80d-450239d5889c")[Lemma 36] that
    $constant_(star)$ is also an equivalence. Consequently, the type $A$ is
    contractible by #link("note://41e67f5f-60c1-4549-8e24-160141e4bd64")[Lemma
    34].
]
