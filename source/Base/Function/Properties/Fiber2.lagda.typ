#import("../../../../../../library/template.typ"): *

#show: template

```agda
module Base.Function.Properties.Fiber2 where

open import Base.Universe.Core
open import Base.Function.Core
open import Base.Function.Definitions
open import Base.Identity.Core
open import Base.Identity.Definitions as Identity
open import Base.Identity.Properties
open import Data.Sigma.Core
open import Data.Sigma.Definitions
open import Data.Sigma.Properties.Equivalence
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

fiber⁻¹-isEquivalence :
  {i j : Level} {A : Type i} {B : Type j}
  (f : A → B) (x : A) →
  IsEquivalence $ fiber⁻¹ f x
fiber⁻¹-isEquivalence f x =
  familyOfEquivalences→totalIsEquivalence
    (λ y → Identity._⁻¹) (λ y → ⁻¹-isEquivalence)
```
