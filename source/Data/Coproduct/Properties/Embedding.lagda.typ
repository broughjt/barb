#import("../../../../../../library/template.typ"): *

#show: template

```agda
module Data.Coproduct.Properties.Embedding where

open import Base.Family.Properties
open import Base.Function.Core
open import Base.Function.Definitions
open import Base.Function.Properties.Contractible
open import Base.Identity.Core
open import Base.Identity.Definitions
open import Base.Identity.Properties
open import Base.Truncation.Definitions
open import Base.Truncation.Properties.Contractible
open import Base.Universe.Core
open import Base.Universe.Lift
open import Data.Coproduct.Core
open import Data.Coproduct.Definitions as Coproduct
open import Data.Coproduct.Properties.Identity
open import Data.Sigma.Core
open import Data.Sigma.Definitions
open import Data.Sigma.Properties.Equivalence
```

= Coproduct injections are embeddings <note:84660b09-4b92-4db3-8c38-7d91afd08b79>
 
#lemma(supplement: cite_link(<rijke2025>, "Rijke 2025, exer. 11.1(b)"))[
    For all types $A$ and $B$, the
    #link("note://001d31c7-7fb6-4878-883a-ff464bb9c0a8")[coproduct injections]
    $
        inject1 ofType A & -> A + B, \
        inject2 ofType B & -> A + B
    $
    are #link("note://cce94748-d9b3-4795-a3d8-c698b6dff9dd")[embeddings].
]
#proof[
    We show that the first injection $inject1$ is an embedding; the argument for
    the second injection is analogous.

    Fix $x ofType A$. We need to show that the family of maps
    $
        piType(y, A) x = y -> inject1(x) = inject1(y)
    $

    given by the #link("note://7caf7ee0-9e2a-4761-bee9-25cd52820039")[action on
    paths] is an
    #link("note://32c2ca55-63ba-411b-9052-676a51fd16a1")[equivalence]. By
    #link("note://47c2a4df-e0c1-49a6-8ce8-feae75d30105")[the fundamental theorem
    of identity types], it suffices to show that the type
    $
        sigmaType(y, A) inject1(x) = inject1(y)
    $

    is #link("note://f817901c-750e-4575-a259-d83730424ade")[contractible]. Using
    the #link("note://a58c0c4a-1fe6-4bf1-8aec-1cfc5ca262ee")[characterization of
    the identity types of coproducts], there is a family of equivalences

    $
        x = y -> inject1(x) = inject1(y)
    $

    indexed by $y ofType A$. By
    #link("note://1e59ed56-2044-4945-8e7e-c97df7680b26")[Theorem 45], it follows
    that the induced map on total spaces is an equivalence, i.e. we have

    $
        sigmaType(y, A) x = y tilde.eq sigmaType(y, A) inject1(x) = inject1(y)
    $

    The type $sigmaType(y, A) x = y$ of endpoint-path pairs is contractible by
    #link("note://0505440a-b3cf-41ad-b847-df4a87400d7a")[Theorem 46]. It follows
    that $sigmaType(y, A) inject1(x) = inject1(y)$ is contractible, since
    contractibility is preserved by equivalences by
    #link("note://41aea79b-658b-464d-b9c4-0326602aa2db")[Lemma 42].
]

```agda
inject₁-isEmbedding :
  {i j : Level} {A : Type i} {B : Type j} →
  IsEmbedding (inject₁ {A = A} {B = B})
inject₁-isEmbedding {A = A} x =
  totalIsContractible→characterize-＝
    x (λ y → pathAction inject₁) r
  where
  f : (y : A) → inject₁ x ＝ inject₁ y → x ＝ y
  f y = (lower ∘ (＝→reflexive {R = Coproduct.Equal} equalReflexive))

  p : (y : A) → IsEquivalence $ f y
  p y = project₂ $ ＝≃Equal₁₁ x y

  q : IsEquivalence $ total f
  q = familyOfEquivalences→totalIsEquivalence f p

  r : IsContractible $ Σ A (λ y → inject₁ x ＝ inject₁ y)
  r = isEquivalence→isContractible→isContractible₂
        (total f) q 
        (endpointPathContractible x)

inject₂-isEmbedding : 
  {i j : Level} {A : Type i} {B : Type j} →
  IsEmbedding (inject₂ {A = A} {B = B})
inject₂-isEmbedding {B = B} x =
  totalIsContractible→characterize-＝
    x (λ y → pathAction inject₂) r
  where
  f : (y : B) → inject₂ x ＝ inject₂ y → x ＝ y
  f y = (lower ∘ (＝→reflexive {R = Coproduct.Equal} equalReflexive))

  p : (y : B) → IsEquivalence $ f y
  p y = project₂ $ ＝≃Equal₂₂ x y

  q : IsEquivalence $ total f
  q = familyOfEquivalences→totalIsEquivalence f p

  r : IsContractible $ Σ B (λ y → inject₂ x ＝ inject₂ y)
  r = isEquivalence→isContractible→isContractible₂
        (total f) q 
        (endpointPathContractible x)
```

= Coproduct recursion is an embedding if and only if both component maps are embeddings with disjoint images <note:bf86af6f-9459-4c21-8107-baa752c657f8>
 
#lemma(supplement: cite_link(<rijke2025>, "Rijke 2025, exer. 11.6"))[
    Let $f ofType A -> C$ and $g ofType B -> C$ be maps. Then the following are
    #link("note://27061ddb-2091-46c1-8752-21db2ab57f44")[logically equivalent]:

    1. The coproduct recursor $[f, g] ofType A + B -> C$ is an embedding.
    2. Both $f$ and $g$ are embeddings, with
       $
           f(x) != g(y)
       $
       for all $x ofType A$ and $y ofType B$.
]
#proof[
]

TODO: Leaving this for the next chapter when we have a much nicer
characterization of embeddings as maps with propositional fibers

Use that for the converse direction, the forward direction follows by precomposing with the injections and using the previous lemmas

```agda

```
