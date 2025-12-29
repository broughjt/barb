#import("../../../../../../library/template.typ"): *

#show: template

```agda
-- TODO: Agda Cubical page says to just ignore these I guess
{-# OPTIONS -WnoUnsupportedIndexedMatch #-}

module Data.Sigma.Properties.Identity where

open import Base.Family.Definitions
open import Base.Family.Properties
open import Base.Function.Core
open import Base.Function.Definitions
open import Base.Function.Properties.Equivalence
open import Base.Identity.Core
open import Base.Universe.Core
open import Data.Sigma.Core
open import Data.Sigma.Definitions
```

= Characterization of identity types of sigma types is reflexive <note:5dece7a8-8e58-4afb-9cb1-91856df227fd>
 
#lemma(
    label: "12",
    supplement: cite_link(<rijke2025>, "Rijke 2025, lem. 9.3.2")
)[
    The #link("note://f7ad6df3-6479-4772-b911-5702cd9e6202")[characterizing
    family for the identity types of sigma types] is
    #link("note://7e7a1c6f-6051-4526-83e9-01d030717ea5")[reflexive].
]
#proof[
    By #link("note://ae098784-7572-4d29-b548-a2db9b6d004a")[$Sigma$-induction],
    it suffices to construct a function
    $
        piType(x, A) piType(y, B(x)) sigmaType(alpha, x = x) tr_(B)(alpha, y) = y.
    $
    Let $x ofType A$ and $y ofType B(x)$. Since
    #link("note://1229c654-047b-4517-9f4c-df4c03224d02")[transport is defined
    using path induction], we have
    $
        tr_(B)(refl_(x), y) dot(eq) y
    $
    #link("note://a0baf580-5da2-4328-bfbd-202bedf37747")[judgementally]. It
    follows that we can simply take $(refl_(x), refl_(y)) ofType
    sigmaType(alpha, x = x) tr_(B)(alpha, y) = y$, completing the construction.
]

```agda
equalReflexive : {i j : Level} {A : Type i} {B : A → Type j} →
                 Reflexive (Equal {A = A} {B = B})
equalReflexive (pair x y) = pair reflexive reflexive
```

= Characterization of identity types of sigma types is equivalent to identity <note:a123eb52-0ec7-4d04-a780-e6761d564fd9>

The #link("note://f7ad6df3-6479-4772-b911-5702cd9e6202")[characterization of the
identity types of $Sigma$-types] is
#link("note://32c2ca55-63ba-411b-9052-676a51fd16a1")[equivalent] to the
#link("note://261490cb-2887-4247-9a83-7f674e3c9651")[identity types] of
#link("note://ae098784-7572-4d29-b548-a2db9b6d004a")[$Sigma$-types].
 
#theorem(supplement: cite_link(<rijke2025>, "Rijke 2025, thm. 9.3.4"))[
    Let $B$ be a #link("note://b05d0e2e-b6ab-45ab-9277-9559f4ee5e1f")[family]
    over a type $A$. For every $u, v ofType sigmaType(x, A) B(x)$, the
    #link("note://d25ccc40-b51e-466f-b87a-59be3acfa38a")[canonical map]
    $
        u = v -> EqualSigma(u, v)
    $
    induced by #link("note://5dece7a8-8e58-4afb-9cb1-91856df227fd")[reflexivity]
    is an #link("note://32c2ca55-63ba-411b-9052-676a51fd16a1")[equivalence].
]
#proof[
    Let
    $
        f ofType piType(u, v, sigmaType(x, A) B(x)) u = v -> EqualSigma(u, v)
    $
    denote the map given by
    #link("note://d25ccc40-b51e-466f-b87a-59be3acfa38a")[Lemma 11] (which shows
    that there is a canonical map from
    #link("note://261490cb-2887-4247-9a83-7f674e3c9651")[identity types] into
    #link("note://7e7a1c6f-6051-4526-83e9-01d030717ea5")[reflexive] type
    families) applied to
    #link("note://5dece7a8-8e58-4afb-9cb1-91856df227fd")[Lemma 12] (which shows
    that $EqualSigma$ is indeed reflexive).

    To define the maps
    $
        g ofType piType(u, v, sigmaType(x, A) B(x)) EqualSigma(u, v) -> u = v
    $
    in the reverse direction, first apply
    #link("note://ae098784-7572-4d29-b548-a2db9b6d004a")[$Sigma$-induction], so
    that it suffices to construct a map
    $
        (sigmaType(alpha, x = x') tr_(B)(alpha, y) = y') -> (x, y) = (x', y')
    $
    for each $(x, y), (x', y') ofType sigmaType(x, A) B(x)$. Applying
    $Sigma$-induction again, it suffices to construct functions
    $
        piType(alpha, x = x') tr_(B)(alpha, y) = y' -> (x, y) = (x', y').
    $
    Using double #link("note://261490cb-2887-4247-9a83-7f674e3c9651")[path
    induction] and the
    #link("note://1229c654-047b-4517-9f4c-df4c03224d02")[definition of
    transport], it suffices to provide a path of type $(x, y) = (x, y)$, so we
    take $refl_((x, y))$.
    
    We claim that $f$ and $g$ are
    #link("note://32c2ca55-63ba-411b-9052-676a51fd16a1")[inverses]. To show
    this, we need to construct
    #link("note://3cb1b8ca-2a77-4c8a-b726-ed8f10dfd208")[homotopies]
    $
        H ofType & g compose f ~ id_(u = v). \
        K ofType & f compose g ~ id_(EqualSigma(u, v)),
    $
    For $K$, we need to provide an identification
    $
        g(f(p)) = p
    $
    for each $p ofType (x, y) = (x', y')$. Proceeding by path induction on $p$,
    the function $f$ applied to $refl_((x, y)) ofType (x, y) = (x, y)$ evaluates
    to
    $
        f(refl_((x, y))) dot(eq) (refl_(x), refl_(y))
    $
    (see proof of #link("note://5dece7a8-8e58-4afb-9cb1-91856df227fd")[Lemma
    12]), so it remains to construct an identification
    $
        g((refl_(x), refl_(y))) = refl_((x, y)),
    $
    and indeed, this holds
    #link("note://a0baf580-5da2-4328-bfbd-202bedf37747")[judgementally] by the
    definition of $g$, so we take $refl_(refl_((x, y)))$.

    To construct $K$, we need to construct an identification
    $
        f(g((alpha, beta))) = (alpha, beta)
    $
    for each $(alpha, beta) ofType sigmaType(alpha, x = x') tr_(B)(alpha, y) =
    y'$. By double path induction on both $alpha$ and $beta$, it suffices to
    construct an identification
    $
        f(g((refl_(x), refl_(y)))) = (refl_(x), refl_(y)).
    $
    This holds judgementally, since $g((refl_(x), refl_(y))) dot(eq) refl_((x,
    y))$ and $f(refl_((x, y))) dot(eq) (refl_(x), refl_(y))$. Therefore, we can
    take $refl_((refl_(x), refl_(y)))$ to complete the construction of $K ofType
    f compose g ~ id$.
]

```agda
＝→equal-isEquivalence :
  {i j : Level} {A : Type i} {B : A → Type j}
  {u v : Σ A B} →
  IsEquivalence (＝→reflexive {R = Equal} equalReflexive {x = u} {y = v})
＝→equal-isEquivalence {A = A} {B = B} {u = (pair x y)} {v = (pair x' y')} =
  inverse→isEquivalence f g (pair H K)
  where
  f : pair x y ＝ pair x' y' → Equal (pair x y) (pair x' y')
  f = ＝→reflexive {R = Equal} equalReflexive {x = pair x y} {y = pair x' y'}

  g : Equal (pair x y) (pair x' y') → pair x y ＝ pair x' y'
  g (pair reflexive reflexive) = reflexive

  H : g ∘ f ∼ identity {_} {pair x y ＝ pair x' y'}
  -- TODO: See -WnoUnsupportedIndexedMatch comment near OPTIONS at the top of
  -- the file
  H reflexive = reflexive

  K : f ∘ g ∼ (identity {_} {Equal (pair x y) (pair x' y')})
  K (pair reflexive reflexive) = reflexive

＝≃Equal :
  {i j : Level} {A : Type i} {B : A → Type j}
  (u v : Σ A B) →
  u ＝ v ≃ Equal u v
＝≃Equal u v = pair (＝→reflexive equalReflexive) ＝→equal-isEquivalence

＝↔Equal : 
  {i j : Level} {A : Type i} {B : A → Type j}
  (u v : Σ A B) →
  u ＝ v ↔ Equal u v
＝↔Equal u v = ≃→↔ $ ＝≃Equal u v

＝→Equal : 
  {i j : Level} {A : Type i} {B : A → Type j}
  {u v : Σ A B} →
  u ＝ v → Equal u v
＝→Equal {u = u} {v = v} = project₁ $ ＝↔Equal u v

Equal→＝ : 
  {i j : Level} {A : Type i} {B : A → Type j}
  {u v : Σ A B} →
  Equal u v → u ＝ v
Equal→＝ {u = u} {v = v} = project₂ $ ＝↔Equal u v
```

= Characterization of product identity types is reflexive <note:e14a7c2e-f533-4cb5-9c7c-959524947706>
 
#lemma[
    The #link("note://dbc89e73-b38a-49b8-b20e-06a10e62393b")[characterizing
    family for product identity types] is
    #link("note://7e7a1c6f-6051-4526-83e9-01d030717ea5")[reflexive].
]
#proof[
    For each $(x, y) ofType A times B$, take the
    #link("note://261490cb-2887-4247-9a83-7f674e3c9651")[paths] $refl_(x) ofType
    x = x$ and $refl_(y) ofType y = y$.
]

```agda
equalReflexive-× : {i j : Level} {A : Type i} {B : Type j} →
                   Reflexive (Equal-× {A = A} {B = B})
equalReflexive-× (pair x y) = pair reflexive reflexive
```

= Characterization of product identity types is equivalent to product identity types <note:1ae1d85f-80d3-4f1d-9d29-8b89ddac166b>
 
#lemma[
    Let $A$ and $B$ be types. For each $u, v ofType A times B$, the
    #link("note://d25ccc40-b51e-466f-b87a-59be3acfa38a")[canonical map]
    $
        (u = v) -> Equal_(times)(u, v)
    $
    induced by #link("note://e14a7c2e-f533-4cb5-9c7c-959524947706")[reflexivity]
    is an #link("note://32c2ca55-63ba-411b-9052-676a51fd16a1")[equivalence].
]
#proof[
    There is a natural inverse map and the required homotopies follow
    essentially for free.
]

See #link("note://dbc89e73-b38a-49b8-b20e-06a10e62393b")[Characterization of
product identity types],
#link("note://f7ad6df3-6479-4772-b911-5702cd9e6202")[Characterization of the
identity types of sigma types], and
#link("note://a123eb52-0ec7-4d04-a780-e6761d564fd9")[Characterization of
identity types of sigma types is equivalent to identity].

```agda
＝→equal-×-isEquivalence :
  {i j : Level} {A : Type i} {B : Type j}
  (u v : A × B) →
  IsEquivalence (＝→reflexive {R = Equal-×} equalReflexive-× {x = u} {y = v})
＝→equal-×-isEquivalence {A = A} {B = B} u@(pair x y) v@(pair x' y') =
  inverse→isEquivalence (＝→reflexive equalReflexive-×) g (pair G H)
  where
  g : (project₁ u ＝ project₁ v) × (project₂ u ＝ project₂ v) → u ＝ v
  g (pair reflexive reflexive) = reflexive

  G : g ∘ (＝→reflexive {R = Equal-×} equalReflexive-×) ∼ identity {_} {u ＝ v}
  G reflexive = reflexive

  H : ＝→reflexive equalReflexive-× ∘ g ∼
      identity {_} {(project₁ u ＝ project₁ v) × (project₂ u ＝ project₂ v)}
  H (pair reflexive reflexive) = reflexive

＝≃Equal-× :
  {i j : Level} {A : Type i} {B : Type j}
  (u v : A × B) →
  u ＝ v ≃ Equal-× u v
＝≃Equal-× u v = pair (＝→reflexive equalReflexive-×) (＝→equal-×-isEquivalence u v)

＝↔Equal-× :
  {i j : Level} {A : Type i} {B : Type j}
  (u v : A × B) →
  u ＝ v ↔ Equal-× u v
＝↔Equal-× u v = ≃→↔ $ ＝≃Equal-× u v

＝→Equal-× : 
  {i j : Level} {A : Type i} {B : Type j}
  {u v : A × B} →
  u ＝ v → Equal-× u v
＝→Equal-× {u = u} {v = v} = project₁ $ ＝↔Equal-× u v

Equal-×→＝ : 
  {i j : Level} {A : Type i} {B : Type j}
  {u v : A × B} →
  Equal-× u v → u ＝ v
Equal-×→＝ {u = u} {v = v} = project₂ $ ＝↔Equal-× u v
```
