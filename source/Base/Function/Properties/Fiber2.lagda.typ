#import("../../../../../../library/template.typ"): *

#show: template

```agda
module Base.Function.Properties.Fiber2 where

open import Base.Function.Core
open import Base.Function.Definitions hiding (_∙_; _⁻¹)
open import Base.Function.Properties.Equivalence
open import Base.Identity.Core
open import Base.Identity.Definitions as Identity
open import Base.Identity.Properties
open import Base.Identity.Syntax
open import Base.Universe.Core
open import Data.Sigma.Core
open import Data.Sigma.Definitions
open import Data.Sigma.Properties.Equivalence
open import Data.Sigma.Properties.Identity
```

= Fiber inverse equivalence <note:215dd04d-4936-402a-86d1-a6c440ce962a>
 
#lemma(label: "52")[
    Let $f ofType A -> B$ be a function. For each $x ofType A$, there is an
    #link("note://32c2ca55-63ba-411b-9052-676a51fd16a1")[equivalence]
    $
        Fiber_(f)(f(x)) dot(eq) sigmaType(y, A) f(y) = f(x) tilde.eq
        sigmaType(y, A) f(x) = f(y)
    $
]
#proof[
    Fix $x ofType A$. By definition, the
    #link("note://96d1fb9a-fd38-48cc-886f-7643637ac1e7")[fiber] of $f$ over
    $f(x)$ is,
    $
        Fiber_(f)(f(x)) dot(eq) sigmaType(y, A) f(y) dot(eq) f(x).
    $
    By #link("note://502e4b53-5266-4e05-9a62-48caa2a3d3e1")[Lemma 51],
    #link("note://95e3c813-ae44-4341-ac56-286cda078568")[inversion of paths]
    defines a #link("note://60d115f9-9bef-47af-916a-1a60ea0b3456")[family of
    equivalences]
    $
        f(y) = f(x) -> f(x) -> f(y)
    $
    indexed by $y ofType A$, so it follows by
    #link("note://1e59ed56-2044-4945-8e7e-c97df7680b26")[Theorem 45] that the
    #link("note://6561eded-451d-46bb-8194-c64a0acf904e")[induced map on total
    spaces]
    $
        sigmaType(y, A) f(y) = f(x) -> sigmaType(y, A) f(x) = f(y)
    $
    is also an equivalence. Hence the claim.
]

See #link("note://96d1fb9a-fd38-48cc-886f-7643637ac1e7")[Fiber of a function
over a point].

```agda
fiber⁻¹ :
  {i j : Level} {A : Type i} {B : Type j}
  (f : A → B) (x : A) →
  Σ A (λ y → f y ＝ f x) → Σ A (λ y → f x ＝ f y)
fiber⁻¹ f x = total (λ y → Identity._⁻¹)

fiber⁻¹' :
  {i j : Level} {A : Type i} {B : Type j}
  (f : A → B) (x : A) →
  Σ A (λ y → f x ＝ f y) → Σ A (λ y → f y ＝ f x)
fiber⁻¹' f x = total (λ y → Identity._⁻¹)

fiber⁻¹-inverse :
  {i j : Level} {A : Type i} {B : Type j}
  (f : A → B) (x : A) →
  Inverse (fiber⁻¹ f x) (fiber⁻¹' f x)
fiber⁻¹-inverse f x =
  familyOfInverses→totalInverse (λ y → _⁻¹) (λ y → _⁻¹) (λ y → ⁻¹⁻¹-inverse)

fiber⁻¹'-inverse :
  {i j : Level} {A : Type i} {B : Type j}
  (f : A → B) (x : A) →
  Inverse (fiber⁻¹' f x) (fiber⁻¹ f x)
fiber⁻¹'-inverse f x =
  inverseInverse (fiber⁻¹ f x) (fiber⁻¹' f x) (fiber⁻¹-inverse f x)

fiber⁻¹-isEquivalence :
  {i j : Level} {A : Type i} {B : Type j}
  (f : A → B) (x : A) →
  IsEquivalence $ fiber⁻¹ f x
fiber⁻¹-isEquivalence f x =
  inverse→isEquivalence (fiber⁻¹ f x) (fiber⁻¹' f x) (fiber⁻¹-inverse f x)

fiber⁻¹'-isEquivalence :
  {i j : Level} {A : Type i} {B : Type j}
  (f : A → B) (x : A) →
  IsEquivalence $ fiber⁻¹' f x
fiber⁻¹'-isEquivalence f x =
  inverse→isEquivalence (fiber⁻¹' f x) (fiber⁻¹ f x) (fiber⁻¹'-inverse f x)
```

= Homotopy induces an equivalence between fibers <note:87f106a8-6338-4411-940e-1b13aa3ccad7>
 
#lemma(label: "71")[
    Let $f, g ofType A -> B$ and let $H ofType f ~ g$. Then for each $y ofType B$,
    there is an
    #link("note://32c2ca55-63ba-411b-9052-676a51fd16a1")[equivalence]
    $
        Fiber_(f)(y) tilde.eq Fiber_(f')(y)
    $
    (see #link("note://96d1fb9a-fd38-48cc-886f-7643637ac1e7")[Fiber of a
    function over a point]).
]
#proof[
    Fix $y ofType
    B$. #link("note://96d1fb9a-fd38-48cc-886f-7643637ac1e7")[Recall that]
    $
        Fiber_(f)(y) dot(eq) sigmaType(x, A) f(x) = y, quad Fiber_(g)(y) dot(eq) sigmaType(x, A) g(x) = y.
    $
    For each $x ofType A$, consider the functions
    $
        phi_(x) & ofType f(x) = y -> g(x) = y, & phi_(x)(p) & := H(x)^(-1) dot.op p, \
        psi_(x) & ofType g(x) = y -> f(x) = y, & psi_(x)(q) & := H(x) dot.op q.
    $

    #link("note://a0b593a9-3e6c-47b8-8160-d8ab79c4dd9b")[Lemma 13] shows that
    $phi_(x)$ and $psi_(x)$ are
    #link("note://32c2ca55-63ba-411b-9052-676a51fd16a1")[inverses] for each $x$.

    These famlies #link("note://6561eded-451d-46bb-8194-c64a0acf904e")[induce
    maps on total spaces]
    $
        total(phi) & ofType sigmaType(x, A) f(x) = y -> sigmaType(x, A) g(x) = y, \
        total(psi) & ofType sigmaType(x, A) g(x) = y -> sigmaType(x, A) f(x) = y.
    $

    Since $phi_x$ and $psi_x$ are inverses for each $x$, it follows by
    #link("note://2d568ea6-459f-476e-9a8b-2d5ea7a57815")[Lemma 70] that
    $total(phi)$ and $total(psi)$ are inverses.

    Hence $Fiber_(f)(y)$ and $Fiber_(g)(y)$ are
    #link("note://32c2ca55-63ba-411b-9052-676a51fd16a1")[equivalent].
]

```agda
fiber∼⁻¹ :
  {i j : Level} {A : Type i} {B : Type j}
  {f g : A → B} →
  f ∼ g →
  ((y : B) → Fiber f y → Fiber g y)
fiber∼⁻¹ {_} {_} {A} {B} {f} {g} H y = total (λ x → _∙_ (H x ⁻¹))

fiber∼ : 
  {i j : Level} {A : Type i} {B : Type j}
  {f g : A → B} →
  f ∼ g →
  ((y : B) → Fiber g y → Fiber f y)
fiber∼ {_} {_} {A} {B} {f} {g} H y = total (λ x → _∙_ (H x))

fiber∼⁻¹-inverse : 
  {i j : Level} {A : Type i} {B : Type j}
  {f g : A → B}
  (H : f ∼ g)
  (y : B) →
  Inverse (fiber∼⁻¹ H y) (fiber∼ H y)
fiber∼⁻¹-inverse {_} {_} {A} {B} {f} {g} H y =
  familyOfInverses→totalInverse
    (λ x → _∙_ (H x ⁻¹))
    (λ x → _∙_ (H x))
    (λ x → ∙⁻¹-inverse (H x))

fiber∼-inverse :
  {i j : Level} {A : Type i} {B : Type j}
  {f g : A → B}
  (H : f ∼ g)
  (y : B) →
  Inverse (fiber∼ H y) (fiber∼⁻¹ H y)
fiber∼-inverse H y =
  inverseInverse (fiber∼⁻¹ H y) (fiber∼ H y) (fiber∼⁻¹-inverse H y)

fiber∼⁻¹-isEquivalence :
  {i j : Level} {A : Type i} {B : Type j}
  {f g : A → B}
  (H : f ∼ g)
  (y : B) →
  IsEquivalence (fiber∼⁻¹ H y)
fiber∼⁻¹-isEquivalence  H y =
  inverse→isEquivalence (fiber∼⁻¹ H y) (fiber∼ H y) (fiber∼⁻¹-inverse H y)

fiber∼-isEquivalence :
  {i j : Level} {A : Type i} {B : Type j}
  {f g : A → B}
  (H : f ∼ g)
  (y : B) →
  IsEquivalence (fiber∼ H y)
fiber∼-isEquivalence H y =
  -- Well, he hands you a nickel, he hands you a dime \ He asks you with a grin
  -- if you're havin' a good time
  inverse→isEquivalence (fiber∼ H y) (fiber∼⁻¹ H y) (fiber∼-inverse H y)
```
