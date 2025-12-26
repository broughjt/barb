#import("../../../../../../library/template.typ"): *

#show: template

```agda
module Data.Sigma.Properties.Truncation where

open import Base.Function.Core
open import Base.Function.Definitions hiding (_⁻¹; _∙_)
open import Base.Function.Properties.Contractible
open import Base.Function.Properties.Equivalence
open import Base.Identity.Core
open import Base.Identity.Definitions
open import Base.Identity.Properties
open import Base.Truncation.Definitions
open import Base.Universe.Core
open import Data.Sigma.Core
open import Data.Sigma.Definitions
open import Data.Sigma.Properties.Equivalence
open import Data.Sigma.Properties.Identity
```

= Cartesian product contractible if and only if both components are contractible <note:61774716-8c8a-4461-a44f-63d9eb7c0244>
 
#lemma(supplement: cite_link(<rijke2025>, "Rijke 2025, exer. 10.5"))[
    For all types $A$ and $B$, the
    #link("note://23a01b78-e433-4a66-8915-bfda82ee149a")[product] $A times B$ is
    #link("note://f817901c-750e-4575-a259-d83730424ade")[contractible] if and
    only if both $A$ and $B$ are contractible.
]
#proof[

    ($==>$) Suppose $A times B$ is
    #link("note://f817901c-750e-4575-a259-d83730424ade")[contractible]. It
    suffices to show that $A$ is contractible, since the contractibility of $B$
    follows by a symmetry argument. Indeed, if $A times B$ is contractible then
    $B times A$ is contractible by Lemma x, which shows that $swap ofType A
    times B -> B times A$ is an equivalence, and Lemma y, which shows that if
    one side of an equivalence is contractible then so is the other. Then we can
    apply the argument to the contractibility of $B times A$ to prove that $B$
    is contractible.
    
]

```agda
×-isContractible→isContractible₁ :
  {i j : Level} {A : Type i} {B : Type j} →
  IsContractible (A × B) → IsContractible A
×-isContractible→isContractible₁ {A = A} (pair (pair c d) C) = pair c C'
  where
  C' : (x : A) → c ＝ x
  -- TODO: Replace with Cartesian product identity characterization
  C' x = project₁ $ ＝→Equal $ C (pair x d)

×-isContractible→isContractible₂ :
  {i j : Level} {A : Type i} {B : Type j} →
  IsContractible (A × B) → IsContractible B
×-isContractible→isContractible₂ {A = A} {B = B} =
  ×-isContractible→isContractible₁ {A = B} {B = A} ∘
  isEquivalence→isContractible→isContractible₁ swap swapIsEquivalence

-- TODO: Replace with Cartesian product identity characterization
-- isContractible→×-isContractible :
--   {i j : Level} {A : Type i} {B : Type j} →
--   IsContractible A → IsContractible B → IsContractible (A × B)
-- isContractible→×-isContractible = {!!}

-- ×-contractible : {i j : Level} {A : Type i} {B : Type j} →
--                  IsContractible (A × B) ↔ (IsContractible A × IsContractible B)
-- ×-contractible {_} {_} {A} {B} = pair
--   (map ×-isContractible→isContractible₁ ×-isContractible→isContractible₂ ∘
--    (λ u → pair u u))
--   (uncurry isContractible→×-isContractible)
```

= Total space over a contractible base space is equivalent to fiber over the center of contraction <note:9f820c12-c050-423b-ae07-cc1fb0cddd37>

#lemma(supplement: cite_link(<rijke2025>, "Rijke 2025, exer. 10.6"))[
    Let $B$ be a #link("note://b05d0e2e-b6ab-45ab-9277-9559f4ee5e1f")[type
    family] over a type $A$. If $A$ is
    #link("note://f817901c-750e-4575-a259-d83730424ade")[contractible] with
    #link("note://f817901c-750e-4575-a259-d83730424ade")[center of contraction]
    $a ofType A$, then the map
    $
        lambda y . (a, y) ofType B(a) -> sigmaType(x, A) B(x)
    $
    is an #link("note://32c2ca55-63ba-411b-9052-676a51fd16a1")[equivalence].
]
#proof[
    Let $A$ be a
    #link("note://f817901c-750e-4575-a259-d83730424ade")[contractible type] with
    #link("note://f817901c-750e-4575-a259-d83730424ade")[center of contraction]
    $a ofType A$ and
    #link("note://f817901c-750e-4575-a259-d83730424ade")[contraction] $C$. We
    may assume without loss of generality that there is a path $C(a)^(-1) =
    refl_(a)$. Indeed, given any contraction $C$, we can always define a new
    contraction
    $
        C'(x) := C(a)^(-1) dot.op C(x)
    $
    which satisfies this requirement by the
    #link("note://ac149ae0-bd8c-4206-a7bf-eb6e7fa1575e")[left inverse law for
    paths] and the
    #link("note://95e3c813-ae44-4341-ac56-286cda078568")[definition of the
    inverse operation].

    Define a map $g ofType sigmaType(x, A) B(x) -> B(a)$ by
    $
        g(x, y) := tr_(B)(C(x)^(-1), y)
    $
    (see #link("note://1229c654-047b-4517-9f4c-df4c03224d02")[Transport along a
    path]). We show that $g$ is an
    #link("note://32c2ca55-63ba-411b-9052-676a51fd16a1")[inverse] of $f :=
    lambda y . (a, y) ofType B(a) -> sigmaType(x, A) B(x)$ by constructing
    #link("note://3cb1b8ca-2a77-4c8a-b726-ed8f10dfd208")[homotopies]
    $
        G ofType & g compose f ~ id_(B(a)), \
        H ofType & f compose g ~ id_(sigmaType(x, A) B(x)).
    $

    For the first homotopy $G$, let $y ofType B(a)$. Then
    $
        g(f(y)) dot(eq) tr_(B)(C(a)^(-1), y).
    $
    Since $C(a)^(-1) = refl_(a)$ by assumption,
    #link("note://1229c654-047b-4517-9f4c-df4c03224d02")[transporting along]
    $C(a)^(-1)$ is is
    #link("note://1229c654-047b-4517-9f4c-df4c03224d02")[judgementally equal] to
    the #link("note://efea6413-096d-4249-8ef0-a4de74fcee13")[identity map], and
    hence there is a path
    $
        tr_(B)(C(a)^(-1), y) = y.
    $

    For the second homotopy $H$, let $(x, y) ofType sigmaType(x, A) B(x)$. We
    must construct a path
    $
        (a, tr_(B)(C(x)^(-1), y)) = (x, y)
    $
    By the
    #link("note://a123eb52-0ec7-4d04-a780-e6761d564fd9")[characterization of
    $Sigma$ identity types], it suffices to give a pair
    $
        sigmaType(p, a = x) tr_(B)(p, tr_(B)(C(x)^(-1), y)) = y.
    $
    Applying the contraction $C$ at $x$ yields a path $p ofType a = x$. By
    #link("note://985f36e7-d07e-4742-ac8c-b7c0dfe1def8")[Lemma 37], which shows
    that transport along inverse paths is an inverse to transport along the
    original path, we obtain the second path
    $
        tr_(B)(C(x), tr_(B)(C(x)^(-1), y)) = y.
    $

    Thus $f$ admits a two sided inverse and is therefore an equivalence.
]

I had the idea to reuse the without loss of generality argument used in
#link("note://dc1d2466-8ead-40b1-9924-f60afcefe390")[Theorem 38] for this proof.

```agda
baseIsContractible→pairEquivalence :
  {i j : Level} {A : Type i} {B : A → Type j}
  (p : IsContractible A) → 
  let a : A
      a = project₁ p
  in IsEquivalence {B = Σ A B} (pair a)
baseIsContractible→pairEquivalence {_} {_} {A} {B} (pair a C) =
  baseIsContractible→pairEquivalence' C' p
  where
  C' : (x : A) → a ＝ x
  C' x = (C a) ⁻¹ ∙ C x

  p : (C' a) ⁻¹ ＝ reflexive
  p = pathAction _⁻¹ $ ⁻¹-inverseˡ (C a)

  baseIsContractible→pairEquivalence' :
    (C : (x : A) → a ＝ x)
    (p : (C a) ⁻¹ ＝ reflexive) →
    IsEquivalence {B = Σ A B} (pair a)
  baseIsContractible→pairEquivalence' C p =
    inverse→isEquivalence (pair a) g (pair G H)
    where
    g : Σ A B → B a
    g (pair x y) = transport B ((C x) ⁻¹) y

    G : g ∘ (pair a) ∼ identity {_} {B a}
    G y = transport (λ ?p → transport B ?p y ＝ y) (p ⁻¹) reflexive

    H : (pair a) ∘ g ∼ identity {_} {Σ A B}
    H (pair x y) =
      Equal→＝ (pair (C x) ((project₂ $ transportInverse (C x)) y))

baseIsContractible⇒fiber≃total :
  {i j : Level} {A : Type i} {B : A → Type j}
  (p : IsContractible A) →
  B (project₁ p) ≃ Σ A B
baseIsContractible⇒fiber≃total p =
  pair (pair $ project₁ p) (baseIsContractible→pairEquivalence p)
```
