#import("../../../../../library/template.typ"): *

#show: template

```agda
module Base.Function.FiberIdentityAlternative where

open import Base.Family.Definitions
open import Base.Family.Properties
open import Base.Function.Core
open import Base.Function.Definitions hiding (_∙_; _⁻¹)
open import Base.Function.Properties.Equivalence
open import Base.Function.Properties.Contractible
open import Base.Identity.Core
open import Base.Identity.Definitions
open import Base.Identity.Properties
open import Base.Truncation.Definitions
open import Base.Truncation.Properties.Contractible
open import Base.Universe.Core
open import Data.Sigma.Core
open import Data.Sigma.Definitions
open import Data.Sigma.Properties.Equivalence
```

= Alternative characterization of fiber identity types <note:86e3a883-739a-4fa2-b2b0-932617c072f5>
 
Following #cite(<rijke2025>, form: "prose", supplement: "ex. 11.6.3"), we give
an alternative characterization of the
#link("note://261490cb-2887-4247-9a83-7f674e3c9651")[identity types] of a
#link("note://96d1fb9a-fd38-48cc-886f-7643637ac1e7")[fiber].

Let $f ofType A -> B$ be a function and fix $y ofType B$. Given two elements
$(x, p)$ and $(x', q)$ of the
#link("note://96d1fb9a-fd38-48cc-886f-7643637ac1e7")[fiber] of $f$ over $y$, our
#link("note://4778d3fd-56f0-4f8f-8810-8440b89e9550")[previous characterization]
says that to identify $(x, p)$ and $(x', q)$, it suffices to give a path $alpha
ofType x = x'$ together with a path
$
    beta ofType p = ap_(f)(alpha) dot.op q,
$
that is, an element of the type
$
    sigmaType(alpha, x = x') p = ap_(f)(alpha) dot.op q.
$

Now observe that we can rearrange $beta$ to obtain a path
$
    ap_(f)(alpha) = p dot.op q^(-1).
$

This suggests that an identification between $(x, p)$ and $(x', q)$ in the fiber
of $f$ over $y$ could instead be described as an element of the fiber

$
    Fiber_(ap_(f))(p dot.op q^(-1)) dot(eq) sigmaType(alpha, x = x') ap_(f)(alpha) = p dot.op q^(-1).
$

Motivated by this, we define the following
#link("note://b05d0e2e-b6ab-45ab-9277-9559f4ee5e1f")[type family].

```agda
Equal' : {i j : Level} {A : Type i} {B : Type j}
         {f : A → B} {y : B} →
         Fiber f y → Fiber f y → Type (i ⊔ j)
Equal' {f = f} (pair x p) (pair x' q) = Fiber (pathAction f) (p ∙ q ⁻¹)
```

This characterization is a bit more fun than the previous one: it views
identifications in a fiber of $f$ as a fiber of the
#link("note://7caf7ee0-9e2a-4761-bee9-25cd52820039")[action on paths] of $f$
over the composite path $p dot.op q^(-1)$.

= Alternative characterization of fiber identity types is reflexive <note:f8e51d73-b612-447c-b5a6-276aa7528906>

#lemma[
    The #link("note://86e3a883-739a-4fa2-b2b0-932617c072f5")[alternative
    characterization of fiber identity types] is
    #link("note://7e7a1c6f-6051-4526-83e9-01d030717ea5")[reflexive].
]
#proof[
    Let $f ofType A -> B$ be a function and fix $y ofType B$. Let $(x, p) ofType
    Fiber_(f)(y)$. We #link("note://7e7a1c6f-6051-4526-83e9-01d030717ea5")[must
    exhibit] an element of
    $
        Equal'((x, p), (x, p)) dot(eq) Fiber_(ap_(f))(p dot.op p^(-1)).
    $
    Take the #link("note://261490cb-2887-4247-9a83-7f674e3c9651")[path]
    $refl_(x) ofType x = x$ for the first component. It therefore suffices to
    produce a path
    $
        ap_(f)(refl_(x)) = p dot.op p^(-1).
    $
    However, we have $ap_(f)(refl_(x)) dot(eq) refl_(f(x))$
    #link("note://7caf7ee0-9e2a-4761-bee9-25cd52820039")[by definition], and we
    have $refl_(f(x)) = p dot.op p^(-1)$ by the
    #link("note://ac149ae0-bd8c-4206-a7bf-eb6e7fa1575e")[right inverse law for
    paths]. This completes the construction.
]

```agda
equalReflexive' : {i j : Level} {A : Type i} {B : Type j}
                  {f : A → B} {y : B} →
                  Reflexive (Equal' {f = f} {y = y})
equalReflexive' (pair x p) = pair reflexive (⁻¹-inverseʳ p ⁻¹)
```

= Alternative characterization of the identity types of fibers is equivalent to their identity types <note:132c18af-533c-4c69-962d-04b3928b792d>

#lemma(supplement: cite_link(<rijke2025>, "Rijke 2025, ex. 11.6.3"))[
    Let $f ofType A -> B$ be a map and fix $y ofType B$. For any elements $(x,
    p)$ and $(x', q)$ of the
    #link("note://96d1fb9a-fd38-48cc-886f-7643637ac1e7")[fiber] of $f$ over $y$,
    the #link("note://d25ccc40-b51e-466f-b87a-59be3acfa38a")[canonical map]
    $
        ((x, p) = (x', q)) -> Equal'_(Fiber_(f)(y))((x, p), (x', q))
    $
    induced by #link("note://f8e51d73-b612-447c-b5a6-276aa7528906")[reflexivity]
    is an #link("note://32c2ca55-63ba-411b-9052-676a51fd16a1")[equivalence] (see
    #link("note://86e3a883-739a-4fa2-b2b0-932617c072f5")[Alternative
    characterization of fiber identity types]).
]
#proof[
    Fix $(x, p) ofType Fiber_(f)(y)$. We apply the
    #link("note://c8ded883-fe70-482b-804b-157512315c1f")[structure identity
    principle] to the type $Fiber_(f)(y) dot(eq) sigmaType(x, A) f(x) =
    y$. Define auxiliary famalies $C$ and $D$ by
    $
        C(x') := x = x'
    $
    and
    $
        D'(x', q, alpha) := ap_(f)(alpha) = p dot.op q^(-1).
    $
    With these choices, the structure identity principle reduces the claim to
    showing that the #link("note://ae098784-7572-4d29-b548-a2db9b6d004a")[total
    spaces]
    $
        sigmaType(x', A) C(x') quad "and" quad sigmaType(q, f(x) = y) D(x, q, refl_(x))
    $
    are #link("note://f817901c-750e-4575-a259-d83730424ade")[contractible].

    The type $sigmaType(x', A) x = x'$ of path-endpoint pairs is contractible by
    #link("note://0505440a-b3cf-41ad-b847-df4a87400d7a")[Theorem 46].

    For the second space, note that
    $ap_(f)(refl_(x)) dot(eq) refl_(f(x))$. Hence there is an equivalence
    $
        sigmaType(q, f(x) = y) refl_(f(x)) = p dot.op q^(-1) tilde.eq
        sigmaType(q, f(x) = y) p = q.
    $
    The right-hand side is contractible, again by Theorem 46. Since
    contractibility is preserved by equivalence
    (#link("note://41aea79b-658b-464d-b9c4-0326602aa2db")[Lemma 42]), it follows
    that
    $
        sigmaType(q, f(x) = y) ap_(f)(refl_(x)) = p dot.op q^(-1)
    $
    is contractible as well. This completes the proof.
]

```agda
＝→equal'-isEquivalence :
  {i j : Level} {A : Type i} {B : Type j}
  {f : A → B} {y : B}
  {u v : Fiber f y} →
  IsEquivalence (＝→reflexive {R = Equal'} equalReflexive' {x = u} {y = v})
＝→equal'-isEquivalence {_} {_} {A} {B} {f} {y} {u@(pair x p)} {v@(pair x' q)} =
  componentTotalIsContractible→characterize-＝-structure
    {C = λ x' → x ＝ x'} {D = λ x' q α → pathAction f α ＝ p ∙ q ⁻¹}
    r k
    u
    (λ where (pair x' q) → ＝→reflexive {R = Equal'} equalReflexive'
                             {x = pair x p} {y = pair x' q})
    v
    where
    r : IsContractible (Σ A (λ x' → x ＝ x'))
    r = endpointPathContractible x

    g : (q : f x ＝ y) → reflexive ＝ p ∙ q ⁻¹ → q ＝ p
    g reflexive r = r ∙ (∙-unitʳ p)
  
    h : (q : f x ＝ y) → q ＝ p → reflexive ＝ p ∙ q ⁻¹
    h reflexive r = r ∙ (∙-unitʳ p) ⁻¹
  
    s : (q : f x ＝ y) → IsEquivalence $ g q
    s reflexive = flip∙-isEquivalence (∙-unitʳ p)

    s' : IsEquivalence $ total g
    s' = familyOfEquivalences→totalIsEquivalence g s

    t : IsEquivalence $ total (λ p → _⁻¹)
    t = familyOfEquivalences→totalIsEquivalence
          (λ p → _⁻¹) (λ p → ⁻¹-isEquivalence)

    k : IsContractible
         (Σ (f x ＝ y) (λ q → pathAction f reflexive ＝ p ∙ q ⁻¹))
    k = isEquivalence→isContractible→isContractible₂
          ((total $ λ p → _⁻¹) ∘ (total g))
          (isEquivalenceCompose (total (λ p → _⁻¹)) (total g) t s')
          (endpointPathContractible p)

＝≃Equal' :
  {i j : Level} {A : Type i} {B : Type j}
  {f : A → B} {y : B}
  {u v : Fiber f y} →
  u ＝ v ≃ Equal' u v
＝≃Equal' = pair (＝→reflexive equalReflexive') ＝→equal'-isEquivalence

＝↔Equal' :
  {i j : Level} {A : Type i} {B : Type j}
  {f : A → B} {y : B}
  {u v : Fiber f y} →
  u ＝ v ↔ Equal' u v
＝↔Equal' = ≃→↔ ＝≃Equal'

＝→Equal' :
  {i j : Level} {A : Type i} {B : Type j}
  {f : A → B} {y : B}
  {u v : Fiber f y} →
  u ＝ v → Equal' u v
＝→Equal' = project₁ ＝↔Equal'

Equal'→＝ :
  {i j : Level} {A : Type i} {B : Type j}
  {f : A → B} {y : B}
  {u v : Fiber f y} →
  Equal' u v → u ＝ v
Equal'→＝ = project₂ ＝↔Equal'
```
