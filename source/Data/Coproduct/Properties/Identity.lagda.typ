#import("../../../../../../library/template.typ"): *

#show: template

```agda
module Data.Coproduct.Properties.Identity where

open import Base.Family.Definitions
open import Base.Family.Properties
open import Base.Function.Core
open import Base.Function.Definitions
open import Base.Function.Properties.Contractible
open import Base.Function.Properties.Equivalence
open import Base.Identity.Core
open import Base.Identity.Properties
open import Base.Truncation.Definitions
open import Base.Truncation.Properties.Contractible
open import Base.Universe.Core
open import Base.Universe.Lift
open import Base.Universe.Properties.Lift
open import Data.Coproduct.Core
open import Data.Coproduct.Definitions
open import Data.Empty as Empty
open import Data.Sigma.Core
```

= Observational equality of coproducts is reflexive <note:cb48ff7c-12ae-4b25-ad04-0132edbff96e>
 
#lemma(supplement: cite_link(<rijke2025>, "Rijke 2025, lem. 11.5.3"))[
    #link("note://d30c9670-8903-4e87-8234-c463ce37ad88")[Observational equality
    of coproducts] is
    #link("note://7e7a1c6f-6051-4526-83e9-01d030717ea5")[reflexive].
]
#proof[
    Take $refl$ in both cases.
]

```agda
equalReflexive : {i j : Level} {A : Type i} {B : Type j} →
                 Reflexive (Equal {A = A} {B = B})
equalReflexive (inject₁ x) = lift reflexive
equalReflexive (inject₂ y) = lift reflexive
```

= Observational equality of coproducts characterizes coproduct identity types <note:a58c0c4a-1fe6-4bf1-8aec-1cfc5ca262ee>

#theorem(supplement: cite_link(<rijke2025>, "Rijke 2025, thm. 11.5.1"))[
    Let $A$ and $B$ be types. For every $u, v ofType A + B$, the
    #link("note://d25ccc40-b51e-466f-b87a-59be3acfa38a")[canonical map]
    $
        (u = v) -> Equal_(+)(u, v)
    $
    induced by #link("note://d30c9670-8903-4e87-8234-c463ce37ad88")[reflexivity]
    is an #link("note://32c2ca55-63ba-411b-9052-676a51fd16a1")[equivalence].
    Therefore, there are equivalences
    $
        Equal(inject1(x), inject1(x')) & tilde.eq x = x', \
        Equal(inject1(x), inject2(y')) & tilde.eq emptyType, \
        Equal(inject2(y), inject1(x')) & tilde.eq emptyType, \
        Equal(inject2(y), inject2(y')) & tilde.eq y = y'
    $
    for every $x, x' ofType A$ and $y, y' ofType B$.
]
#proof[
    By #link("note://47c2a4df-e0c1-49a6-8ce8-feae75d30105")[the fundamental
    theorem of identity types], it suffices to show that the type
    $
        sigmaType(v, A + B) Equal(u, v)
    $
    is #link("note://f817901c-750e-4575-a259-d83730424ade")[contractible] for
    each $u ofType A + B$. By case analysis on $u$, this amounts to showing that
    $
        sigmaType(v, A + B) Equal(inject1(x), v) quad "and" quad
        sigmaType(v, A + B) Equal(inject2(y), v)
    $
    are both contractible for all $x ofType A$ and $y ofType B$. We claim that
    there are #link("note://32c2ca55-63ba-411b-9052-676a51fd16a1")[equivalences]
    $
        sigmaType(v, A + B) Equal(inject1(x), v) & tilde.eq sigmaType(x', A) x = x', \
        sigmaType(v, A + B) Equal(inject2(y), v) & tilde.eq sigmaType(y', B) y = y'.
    $
    There are natural maps back and forth, and the
    #link("note://32c2ca55-63ba-411b-9052-676a51fd16a1")[required homotopies]
    hold essentially for free. See the formal proof below for details. Since
    both types of endpoint-path pairs on the right-hand side are contractible by
    #link("note://0505440a-b3cf-41ad-b847-df4a87400d7a")[Lemma 46], and
    contractibility is preserved by equivalences by
    #link("note://41aea79b-658b-464d-b9c4-0326602aa2db")[Lemma 42], it follows
    that the types
    $
        sigmaType(v, A + B) Equal(inject1(x), v) quad "and" quad
        sigmaType(v, A + B) Equal(inject2(y), v)
    $
    are contractible. Hence the claim.
]

```agda
＝→equal-isEquivalence :
  {i j : Level} {A : Type i} {B : Type j}
  {u v : A ＋ B} →
  IsEquivalence (＝→reflexive {R = Equal} equalReflexive {x = u} {y = v})
＝→equal-isEquivalence {_} {_} {A} {B} {u} {v} =
  totalIsContractible→characterize-＝
    (p u) u (λ v → ＝→reflexive equalReflexive) v
  where
  p : (u : A ＋ B) → IsContractible (Σ (A ＋ B) (Equal u))
  p (inject₁ x) =
    isEquivalence→isContractible→isContractible₂
      f q (endpointPathContractible x)
    where
    f : Σ (A ＋ B) (Equal $ inject₁ x) → Σ A (_＝_ x)
    f (pair (inject₁ x') p) = pair x' (lower p)
    f (pair (inject₂ _) p) = Empty.recursion (lower p)

    g : Σ A (_＝_ x) → Σ (A ＋ B) (Equal $ inject₁ x)
    g (pair x p) = pair (inject₁ x) (lift $ p)

    G : g ∘ f ∼ identity {_} {Σ (A ＋ B) (Equal $ inject₁ x)}
    G (pair (inject₁ x) (lift p)) = reflexive
    G (pair (inject₂ y) (lift p)) = Empty.recursion p

    H : f ∘ g ∼ identity {_} {Σ A (_＝_ x)}
    H (pair x' p) = reflexive

    q : IsEquivalence f
    q = inverse→isEquivalence f g (pair G H)
  p (inject₂ y) =
    isEquivalence→isContractible→isContractible₂
      f q (endpointPathContractible y)
    where
    f : Σ (A ＋ B) (Equal $ inject₂ y) → Σ B (_＝_ y)
    f (pair (inject₁ _) p) = Empty.recursion (lower p)
    f (pair (inject₂ y') p) = pair y' (lower p)

    g : Σ B (_＝_ y) → Σ (A ＋ B) (Equal $ inject₂ y)
    g (pair y' p) = pair (inject₂ y') (lift p)

    G : g ∘ f ∼ identity {_} {Σ (A ＋ B) (Equal $ inject₂ y)}
    G (pair (inject₁ x) (lift p)) = Empty.recursion p
    G (pair (inject₂ y) (lift p)) = reflexive

    H : f ∘ g ∼ identity {_} {Σ B (_＝_ y)}
    H (pair y' p) = reflexive

    q : IsEquivalence f
    q = inverse→isEquivalence f g (pair G H)

＝≃Equal :
  {i j : Level} {A : Type i} {B : Type j}
  (u v : A ＋ B) →
  u ＝ v ≃ Equal u v
＝≃Equal u v = pair (＝→reflexive equalReflexive) ＝→equal-isEquivalence

＝↔Equal :
  {i j : Level} {A : Type i} {B : Type j}
  (u v : A ＋ B) →
  u ＝ v ↔ Equal u v
＝↔Equal u v = ≃→↔ (＝≃Equal u v)

＝→Equal :
  {i j : Level} {A : Type i} {B : Type j}
  (u v : A ＋ B) →
  u ＝ v → Equal u v
＝→Equal u v = project₁ $ ＝↔Equal u v

Equal→＝ :
  {i j : Level} {A : Type i} {B : Type j}
  (u v : A ＋ B) →
  Equal u v → u ＝ v
Equal→＝ u v = project₂ $ ＝↔Equal u v

＝≃Equal₁₁ :
  {i j : Level} {A : Type i} {B : Type j}
  (x x' : A) →
  inject₁ {B = B} x ＝ inject₁ x' ≃ x ＝ x'
＝≃Equal₁₁ {i} {j} {A} {B} x x' =
  pair
    (lower ∘ (＝→reflexive {R = Equal} equalReflexive))
    (isEquivalenceCompose lower (＝→reflexive {R = Equal} equalReflexive)
      (lowerIsEquivalence j) ＝→equal-isEquivalence)

＝≃Equal₁₂ :
  {i j : Level} {A : Type i} {B : Type j}
  (x : A) (y : B) →
  inject₁ x ＝ inject₂ y ≃ 𝟎
＝≃Equal₁₂ {i} {j} {A} {B} x y =
  pair
    (lower ∘ (＝→reflexive {R = Equal} equalReflexive))
    (isEquivalenceCompose lower (＝→reflexive {R = Equal} equalReflexive)
      (lowerIsEquivalence (i ⊔ j)) ＝→equal-isEquivalence)

＝≃Equal₂₁ :
  {i j : Level} {A : Type i} {B : Type j}
  (x : A) (y : B) →
  inject₂ y ＝ inject₁ x ≃ 𝟎
＝≃Equal₂₁ {i} {j} {A} {B} x y =
  pair
    (lower ∘ (＝→reflexive {R = Equal} equalReflexive))
    (isEquivalenceCompose lower (＝→reflexive {R = Equal} equalReflexive)
      (lowerIsEquivalence (i ⊔ j)) ＝→equal-isEquivalence)

＝≃Equal₂₂ :
  {i j : Level} {A : Type i} {B : Type j}
  (y y' : B) →
  inject₂ {A = A} y ＝ inject₂ y' ≃ y ＝ y'
＝≃Equal₂₂ {i} {j} {A} {B} x x' =
  pair
    (lower ∘ (＝→reflexive {R = Equal} equalReflexive))
    (isEquivalenceCompose lower (＝→reflexive {R = Equal} equalReflexive)
      (lowerIsEquivalence i) ＝→equal-isEquivalence)
```
