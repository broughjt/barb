#import("../../../../../../library/template.typ"): *

#show: template

```agda
{-# OPTIONS -WnoUnsupportedIndexedMatch #-}

module Base.Function.Properties.Fiber where

open import Base.Universe.Core
open import Base.Function.Core
open import Base.Function.Definitions
open import Base.Function.Properties.Equivalence
open import Base.Identity.Core
open import Base.Identity.Definitions
open import Data.Sigma.Core
open import Data.Sigma.Definitions
open import Data.Sigma.Properties.Identity
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

= Fibers of the induced map on total spaces are equivalent to the fibers of the component maps <note:7a736198-c62d-4ffa-8dc3-30f145d66dab>

Intuitively, this lemma states that for each point $(x, z) ofType sigmaType(x,
A) C(x)$, the #link("note://96d1fb9a-fd38-48cc-886f-7643637ac1e7")[fiber] of the
#link("note://6561eded-451d-46bb-8194-c64a0acf904e")[induced map on total
spaces] $total(f)$ over $(x, z)$ is the same as the fiber of the component map
$f(x) ofType B(x) -> C(x)$ over $z$.
 
#lemma(
    label: "44",
    supplement: cite_link(<rijke2025>, "Rijke 2025, lem. 11.1.2")
)[
    For any family of maps $f ofType piType(x, A) B(x) -> C(x)$ and any $u
    ofType sigmaType(x, A) C(x)$, there is an equivalence
    $
        Fiber_(total(f))(u) tilde.eq Fiber_(f(project1(u)))(project2(u)).
    $
]
#proof[
    Let $x_0 ofType A$ and $z_0 ofType C(x)$. Define a map
    $
        phi ofType Fiber_(total(f))((x_0, z_0)) -> Fiber_(f(x_0))(z_0)
    $

    as follows. An element of the left-hand side fiber consists of a triple
    $((x, y), p)$ where $p ofType (x, f(x, y)) = (x_0, z_0)$. Using the
    #link("note://ae098784-7572-4d29-b548-a2db9b6d004a")[first projection] of
    the #link("note://571b0e34-86b8-4d44-9e85-d862dafc62e2")[characterization of
    $Sigma$ identity types], we obtain a
    #link("note://261490cb-2887-4247-9a83-7f674e3c9651")[path] $p' ofType x =
    x_0$. We may assume $p$ is $refl_(x)$ by
    #link("note://261490cb-2887-4247-9a83-7f674e3c9651")[path induction]. Then
    the #link("note://ae098784-7572-4d29-b548-a2db9b6d004a")[second projection]
    (call it $q$) of the characterization of $Sigma$ identity types has type
    $
        q ofType f(x_0)(y) = z_0.
    $
    Therefore we can set $phi((x, y), p) := (y, q)$.

    For the inverse, define a map
    $
        psi ofType Fiber_(f(x_0))(z_0) -> Fiber_(total(f))((x_0, z_0))
    $
    by sending pairs $(y, p)$, where $p ofType f(x_0)(y) = z_0$, to
    $
        ((x_0, y), alpha)
    $
    where $alpha$ has type $(x_0, f(x_0, y)) = (x_0, z_0)$ and is obtained by
    applying the characterization of $Sigma$ identity types to the paths
    $refl_(x_0)$ and $p$.

    A direct inspection using
    #link("note://ae098784-7572-4d29-b548-a2db9b6d004a")[$Sigma$] and
    #link("note://261490cb-2887-4247-9a83-7f674e3c9651")[path induction] shows
    that there are
    #link("note://3cb1b8ca-2a77-4c8a-b726-ed8f10dfd208")[homotopies]
    $
        psi compose phi ~ id_(Fiber_(total(f))(x_0, z_0)), \
        phi compose psi ~ id_(Fiber_(f(x_0))(z_0))
    $
    Thus $phi$ and $psi$ are inverses, and hence define an equivalence
    $
        Fiber_(total(f))(u) tilde.eq Fiber_(f(project1(u)))(project2(u)).
    $
]

```agda
toFiberTotal :
  {i j k : Level} {A : Type i} {B : A → Type j} {C : A → Type k}
  (f : (x : A) → B x → C x)
  (u : Σ A C) →
  Fiber (total f) u → Fiber (f $ project₁ u) (project₂ u)
toFiberTotal {B = B} f (pair x₀ z₀) (pair (pair x y) p) with (＝→Equal p)
... | pair reflexive q = pair y q

fromFiberTotal :
  {i j k : Level} {A : Type i} {B : A → Type j} {C : A → Type k}
  (f : (x : A) → B x → C x)
  (u : Σ A C) →
  Fiber (f $ project₁ u) (project₂ u) → Fiber (total f) u
fromFiberTotal f (pair x₀ z₀) (pair y p) =
  pair (pair x₀ y) (Equal→＝ (pair reflexive p)) 

toFiberTotalInverse : 
  {i j k : Level} {A : Type i} {B : A → Type j} {C : A → Type k}
  (f : (x : A) → B x → C x)
  (u : Σ A C) →
  Inverse (toFiberTotal f u) (fromFiberTotal f u)
toFiberTotalInverse f (pair x₀ z₀) = pair G H
  where
  G : (fromFiberTotal f (pair x₀ z₀)) ∘ (toFiberTotal f (pair x₀ z₀)) ∼
      identity {_} {Fiber (total f) (pair x₀ z₀)}
  G (pair (pair x y) reflexive) = reflexive

  H : (toFiberTotal f (pair x₀ z₀)) ∘ (fromFiberTotal f (pair x₀ z₀)) ∼
      identity {_} {Fiber (f x₀) z₀}
  H (pair y reflexive) = reflexive

toFiberTotalIsEquivalence :
  {i j k : Level} {A : Type i} {B : A → Type j} {C : A → Type k}
  (f : (x : A) → B x → C x)
  (u : Σ A C) →
  IsEquivalence $ toFiberTotal f u
toFiberTotalIsEquivalence f u =
  inverse→isEquivalence (toFiberTotal f u)
                        (fromFiberTotal f u)
                        (toFiberTotalInverse f u)

fiberTotal≃ : 
  {i j k : Level} {A : Type i} {B : A → Type j} {C : A → Type k}
  (f : (x : A) → B x → C x)
  (u : Σ A C) →
  Fiber (total f) u ≃ Fiber (f $ project₁ u) (project₂ u)
fiberTotal≃ f u = pair (toFiberTotal f u) (toFiberTotalIsEquivalence f u)
```
