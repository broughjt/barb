#import("../../../../../../library/template.typ"): *

#show: template

```agda
module Base.Function.Properties.Fiber where

open import Base.Universe.Core
open import Base.Function.Core
open import Base.Function.Definitions
open import Base.Function.Properties.Equivalence
open import Base.Identity.Core
open import Data.Sigma.Core
```

= Equivalence with the total space of fibers <note:7d81a2c9-bfa4-4509-8ee2-0e5b2ca28f25>
 
#lemma(supplement: cite_link(<rijke2025>, "Rijke 2025, exer. 10.8"))[
    For any map $f ofType A -> B$, there is an
    #link("note://32c2ca55-63ba-411b-9052-676a51fd16a1")[equivalence]
    $
        e ofType A tilde.eq sigmaType(y, B) Fiber_(f)(y)
    $
    equipped with a
    #link("note://3cb1b8ca-2a77-4c8a-b726-ed8f10dfd208")[homotopy] $f ~ project1
    compose e$ witnessing that the triangle

    #let project11 = $#math.sans("project")_(1)$

    #figure(
        diagram($
            A edge("r", e, ->) edge("dr", f, ->, label-side: #right) & sigmaType(x, A) B(x) edge("d", project11, ->, label-side: #left) \
                & X
        $)
    )
    commutes.
]
#proof[
    Define a map
    $
        g ofType A -> sigmaType(y, B) Fiber_(f)(y)
    $
    by $g(x) := (f(x), (x, refl_(f(x))))$. Define its inverse
    $
        h ofType sigmaType(y, B) Fiber_(f)(y) -> A
    $
    by $h((y, (x, p))) := x$. Indeed, these maps are
    #link("note://32c2ca55-63ba-411b-9052-676a51fd16a1")[inverses]: the
    #link("note://28c89bbd-87da-42ef-b825-18c8ab632c2f")[composite] $h compose
    g$ is #link("note://a0baf580-5da2-4328-bfbd-202bedf37747")[judgementally
    equal] to the #link("note://f00d5782-6e4f-4356-80ca-6e02baaf09ac")[identity]
    on $A$, while the composite $g compose h$ can be shown to be homotopic to
    the identity on $sigmaType(y, B) Fiber_(f)(y)$ by using
    #link("note://261490cb-2887-4247-9a83-7f674e3c9651")[path induction]. The
    homotopy
    $
        f ~ project1 compose g
    $
    also holds by definition.
]

In other words, every map factors through the
#link("note://ae098784-7572-4d29-b548-a2db9b6d004a")[total space] of its
#link("note://96d1fb9a-fd38-48cc-886f-7643637ac1e7")[fibers]. According to
#cite(<rijke2025>, form: "prose", supplement: "exer. 10.8"), the projection
$project1 ofType (sigmaType(y, B) Fiber_(f)(y)) -> B$ is sometimes referred to
as the *fibrant replacement* of $f$ because projections play the role of
fibrations in the homotopy interpretation of type theory.

```agda
toTotalFiber : {i j : Level} {A : Type i} {B : Type j}
               (f : A → B) →
               A → Σ B (Fiber f)
toTotalFiber f x = pair (f x) (pair x reflexive)

fromTotalFiber : {i j : Level} {A : Type i} {B : Type j}
                 (f : A → B) →
                 Σ B (Fiber f) → A
fromTotalFiber f (pair y (pair x p)) = x
 
toTotalFiberInverse : {i j : Level} {A : Type i} {B : Type j}
                      (f : A → B) →
                      Inverse (toTotalFiber f) (fromTotalFiber f)
toTotalFiberInverse {_} {_} {A} {B} f = pair G H
  where
  G : (fromTotalFiber f) ∘ (toTotalFiber f) ∼ identity {_} {A}
  G x = reflexive

  H : (toTotalFiber f) ∘ (fromTotalFiber f) ∼ identity {_} {Σ B (Fiber f)}
  H (pair y (pair x reflexive)) = reflexive

toTotalFiberEquivalence : {i j : Level} {A : Type i} {B : Type j}
                          (f : A → B) →
                          IsEquivalence (toTotalFiber f)
toTotalFiberEquivalence f =
  inverse→isEquivalence (toTotalFiber f)
                        (fromTotalFiber f)
                        (toTotalFiberInverse f)

totalFiber≃ : {i j : Level} {A : Type i} {B : Type j}
              (f : A → B) →
              A ≃ Σ B (Fiber f)
totalFiber≃ f = pair (toTotalFiber f) (toTotalFiberEquivalence f)

totalFiberTriangle : {i j : Level} {A : Type i} {B : Type j}
                     (f : A → B) →
                     f ∼ project₁ ∘ (toTotalFiber f)
totalFiberTriangle f x = reflexive
```
