#import("../../../../../../library/template.typ"): *

#show: template

```agda
module Base.Function.Properties.Contractible where

open import Base.Universe.Core
open import Base.Function.Core
open import Base.Function.Definitions
open import Base.Function.FiberIdentity as Fiber
open import Base.Function.Properties.Equivalence
open import Base.Truncation.Definitions
open import Base.Identity.Core
open import Base.Identity.Definitions as Identity
open import Base.Identity.Properties as Identity
open import Base.Identity.Syntax
open import Data.Sigma.Core
```

= Every contractible map is an equivalence <note:e6848e01-6f0e-415e-9010-b0f2e2b28370>
 
#theorem(supplement: cite_link(<rijke2025>, "thm. 10.3.5"))[
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
 
#lemma(supplement: cite_link(<rijke2025>, "Rijke 2025, prop. 10.4.2"))[
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
