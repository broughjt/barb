#import("../../../../../library/template.typ"): *

#show: template

```agda
-- TODO: Agda Cubical page says to just ignore these I guess
{-# OPTIONS -WnoUnsupportedIndexedMatch #-}

module Base.Function.FiberIdentity where

open import Base.Family.Definitions
open import Base.Family.Properties
open import Base.Function.Definitions hiding (_∙_)
open import Base.Function.Core
open import Base.Function.Properties.Equivalence
open import Base.Identity.Core
open import Base.Identity.Definitions
open import Base.Universe.Core
open import Data.Sigma.Core
```

= Characterization of fiber identity types <note:4778d3fd-56f0-4f8f-8810-8440b89e9550>
 
We follow #cite(<rijke2025>, form: "prose", supplement: "def. 10.3.2") in both
the following definition and the preceding motivation.

Consider a function $f ofType A -> B$ and an element $y ofType B$. To
#link("note://261490cb-2887-4247-9a83-7f674e3c9651")[identify] two elements $(x,
p)$ and $(x', p')$ of the
#link("note://96d1fb9a-fd38-48cc-886f-7643637ac1e7")[fiber] of $f$ over $y$, we
must first construct an identification $alpha ofType x = x'$. Then since $p
ofType f(x) = y$ and $p' ofType f(x') = y$, we can form the triangle:

// TODO: Using seperate action on paths because sans is for mathyml and breaks
// in the SVG
#let app = math.sans("ap")

#figure(
    diagram($
        f(x) fletchereq("rr", app_(f)(alpha)) fletchereq("dr", p, label-side: #right) & & f(x') fletchereq("dl", p', label-side: #left) \
            & y
    $)
)

Therefore, may consider identifications $alpha ofType x = x'$ and $beta ofType p
= ap_(f)(alpha) dot.op p'$. Thus we define the following
#link("note://b05d0e2e-b6ab-45ab-9277-9559f4ee5e1f")[type family], intended to
characterize fiber identity types.

```agda
Equal : {i j : Level} {A : Type i} {B : Type j}
        {f : A → B} {y : B} →
        Fiber f y → Fiber f y → Type (i ⊔ j)
Equal {f = f} (pair x p) (pair x' p') =
  Σ (x ＝ x') (λ α → p ＝ (pathAction f α) ∙ p')
```

= Characterization of fiber identity types is reflexive <note:f00502b6-320e-4105-b44b-b3d61c28c59b>
 
#lemma[
    The #link("note://4778d3fd-56f0-4f8f-8810-8440b89e9550")[characterization of
    fiber identity types] is
    #link("note://7e7a1c6f-6051-4526-83e9-01d030717ea5")[reflexive].
]
#proof[
    Suppose $f ofType A -> B$ and $y ofType B$. Let $(x, p) ofType
    Fiber_(f)(y)$. Take $refl_(x) ofType x = x$ for the
    #link("note://4778d3fd-56f0-4f8f-8810-8440b89e9550")[first path]. Since
    $ap_(f)(refl_(x)) dot(eq) refl_(f(x))$ by the
    #link("note://7caf7ee0-9e2a-4761-bee9-25cd52820039")[definition of the
    action on paths], the type $p = ap_(f)(refl_(x)) dot.op p$ evaluates to $p =
    p$, so we can just take $refl_(p)$ for the
    #link("note://4778d3fd-56f0-4f8f-8810-8440b89e9550")[second path].
]

```agda
equalReflexive : {i j : Level} {A : Type i} {B : Type j}
                 {f : A → B} {y : B} →
                 Reflexive (Equal {f = f} {y = y})
equalReflexive (pair x p) = pair reflexive reflexive
```

= Characterization of fiber identity types is equivalent to fiber identity types <note:571b0e34-86b8-4d44-9e85-d862dafc62e2>
 
#lemma(supplement: cite_link(<rijke2025>, "Rijke 2025, prop. 10.3.3"))[
    Let $f ofType A -> B$ be a map and let $y ofType B$. For any elements $(x,
    p)$ and $(x', p')$ of the
    #link("note://96d1fb9a-fd38-48cc-886f-7643637ac1e7")[fiber] of $f$ over $y$,
    the canonical map
    $
        ((x, y) = (x', y)) -> Equal_(Fiber_(f))((x, p), (x', p'))
    $
    #link("note://d25ccc40-b51e-466f-b87a-59be3acfa38a")[induced by] the
    #link("note://f00502b6-320e-4105-b44b-b3d61c28c59b")[reflexivity] of
    $Equal_(Fiber_(f))$ is an
    #link("note://32c2ca55-63ba-411b-9052-676a51fd16a1")[equivalence].
]
#proof[
    To construct the inverse map
    $
        Equal_(Fiber_(f))((x, p), (x', p')) -> (x, p) = (x', p'),
    $
    it suffices by #link("note://ae098784-7572-4d29-b548-a2db9b6d004a")[$Sigma$
    induction], #link("note://261490cb-2887-4247-9a83-7f674e3c9651")[path
    induction], and the definition of the
    #link("note://7caf7ee0-9e2a-4761-bee9-25cd52820039")[action on paths] to
    give a map
    $
        g ofType piType(beta, p = p') (x, p) = (x, p').
    $
    Therefore, we can set $g(beta) := ap_(pair(x))(beta)$. The
    #link("note://3cb1b8ca-2a77-4c8a-b726-ed8f10dfd208")[homotopies] witnessing
    that the canonical map and $g$ are
    #link("note://32c2ca55-63ba-411b-9052-676a51fd16a1")[inverses] then hold by
    definition.
]

```agda
＝→equal-isEquivalence :
  {i j : Level} {A : Type i} {B : Type j}
  {f : A → B} {y : B}
  {u v : Fiber f y} →
  IsEquivalence (＝→reflexive {R = Equal} equalReflexive {x = u} {y = v})
＝→equal-isEquivalence {u = pair x p} {v = pair x' p'} =
  inverse→isEquivalence f g (pair H K)
  where
  f : pair x p ＝ pair x' p' → Equal (pair x p) (pair x' p')
  f = ＝→reflexive {R = Equal} equalReflexive

  g : Equal (pair x p) (pair x' p') → pair x p ＝ pair x' p'
  g (pair reflexive β) = pathAction (pair x) β

  H : g ∘ f ∼ identity {_} {pair x p ＝ pair x' p'}
  H reflexive = reflexive

  K : f ∘ g ∼ identity {_} {Equal (pair x p) (pair x' p')}
  K (pair reflexive reflexive) = reflexive

＝≃Equal :
  {i j : Level} {A : Type i} {B : Type j}
  {f : A → B} {y : B}
  {u v : Fiber f y} →
  u ＝ v ≃ Equal u v
＝≃Equal = pair (＝→reflexive equalReflexive) ＝→equal-isEquivalence
```
