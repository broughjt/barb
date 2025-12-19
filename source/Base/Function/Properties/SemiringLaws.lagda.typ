#import("../../../../../../library/template.typ"): *

#show: template

```agda
module Base.Function.Properties.SemiringLaws where

open import Base.Function.Definitions
open import Base.Function.Negation
open import Base.Function.Properties.Equivalence
open import Base.Universe
open import Data.Coproduct.Core
open import Data.Coproduct.Properties.Negation
open import Data.Empty as Empty
open import Data.Sigma.Core
```

= Coproducts satisfy the unit laws up to equivalence with respect to the empty type <note:f5ac35b4-ac3e-4b2c-984e-28edc4e7c935>

#lemma(supplement: cite_link(<rijke2025>, "Rijke 2025, ex. 9.2.9"))[
    For every type $A$, there are
    #link("note://32c2ca55-63ba-411b-9052-676a51fd16a1")[equivalences]
    $
        0 + A tilde.eq A quad "and" quad A + 0 tilde.eq A.
    $
]
#proof[
    By #link("note://b7b0a00f-26af-486c-b13d-6f5160fbb2d0")[Lemma 6], the maps
    $resolve2 ofType 0 + A -> A$ and $resolve1 ofType A + 0 -> A$ (see
    #link("note://4af48c11-22e0-4aae-89eb-fad6d4320836")[Negation resolution])
    have #link("note://32c2ca55-63ba-411b-9052-676a51fd16a1")[inverses] (namely
    $inject2$ and $inject1$). It follows by
    #link("note://731be08a-a2ad-477a-8c08-d9f26c32de41")[Lemma 3] that
    $resolve2$ and $resolve1$ are equivalences.
]

See #link("note://001d31c7-7fb6-4878-883a-ff464bb9c0a8")[Coproduct type] and
#link("note://9d7cf197-7f2a-4633-aa63-1c9df1429a13")[Empty type].

```agda
＋-unitˡ : {i : Level} (A : Type i) →
           (𝟎 ＋ A) ≃ A
＋-unitˡ A =
  pair (resolve₂ Empty.recursion)
       (hasInverse→isEquivalence
         (pair inject₂ (resolve₂-inject₂-inverse Empty.recursion)))

＋-unitʳ : {i : Level} (A : Type i) →
           (A ＋ 𝟎) ≃ A
＋-unitʳ A =
  pair (resolve₁ Empty.recursion)
       (hasInverse→isEquivalence
         (pair inject₁ (resolve₁-inject₁-inverse Empty.recursion)))
```
