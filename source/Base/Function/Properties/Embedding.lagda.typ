#import("../../../../../../library/template.typ"): *

#show: template

```agda
module Base.Function.Properties.Embedding where

open import Base.Function.Core
open import Base.Function.Definitions
open import Base.Function.Properties.Contractible
open import Base.Function.Properties.Fiber2
open import Base.Identity.Core
open import Base.Identity.Definitions
open import Base.Truncation.Definitions
open import Base.Truncation.Properties.Contractible
open import Base.Universe.Core
open import Data.Sigma.Core
```

= Every equivalence is an embedding <note:577a5656-7132-434f-ba99-a2736940d780>
 
#theorem(supplement: cite_link(<rijke2025>, "Rijke 2025, thm. 11.4.2"))[
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
  totalIsContractible→characterize-＝ x (λ y → pathAction f) r
  where
  q : IsContractible (Fiber f (f x))
  q = isEquivalence→isContractibleFunction p (f x)

  r : IsContractible (Σ A (λ y → f x ＝ f y))
  r = isEquivalence→isContractible→isContractible₁
      (fiber⁻¹ f x)
        (fiber⁻¹-isEquivalence f x)
        q
```
