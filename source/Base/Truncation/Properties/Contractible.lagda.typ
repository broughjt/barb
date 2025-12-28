#import("../../../../../../library/template.typ"): *

#show: template

```agda
module Base.Truncation.Properties.Contractible where

open import Base.Universe.Core
open import Base.Universe.Lift hiding (induction)
open import Base.Universe.Properties.Lift
open import Base.Truncation.Definitions
open import Base.Function.Core
open import Base.Function.Definitions hiding (_⁻¹; _∙_)
open import Base.Function.Properties.Contractible
open import Base.Function.Properties.Equivalence
open import Base.Identity.Core hiding (induction)
open import Base.Identity.Definitions
open import Base.Identity.Properties
open import Base.Identity.IdentitySystem
open import Data.Sigma.Core as Sigma hiding (induction)
open import Data.Sigma.Definitions
open import Data.Sigma.Properties.Equivalence
```

= A type is contractible if and only if it satisfies singleton induction <note:dc1d2466-8ead-40b1-9924-f60afcefe390>
 
#theorem(
    label: "38",
    supplement: cite_link(<rijke2025>, "Rijke 2025, thm. 10.2.3")
)[
    A type is #link("note://f817901c-750e-4575-a259-d83730424ade")[contractible]
    if and only if it satisfies
    #link("note://2a65336f-3db1-411e-869f-9c87a18d408a")[singleton induction].
]

Note: In the proof below, I didn't come up with the reduction to the case where
$C(c) = refl_(c)$. I followed Rijke's proof for this part.  

#proof[
    ($==>$) Let $A$ be a
    #link("note://f817901c-750e-4575-a259-d83730424ade")[contractible type] with
    #link("note://f817901c-750e-4575-a259-d83730424ade")[center of contraction]
    $c$ and #link("note://f817901c-750e-4575-a259-d83730424ade")[contraction]
    $C$. We may assume without loss of generality that $C$ comes equipped with a
    #link("note://261490cb-2887-4247-9a83-7f674e3c9651")[path] $C(c) =
    refl_(c)$. Indeed, given any contraction $C$, we can always define a new
    contraction
    $
        C'(x) := C(c)^(-1) dot.op C(x)
    $
    which satisfies this requirement by the
    #link("note://ac149ae0-bd8c-4206-a7bf-eb6e7fa1575e")[left inverse law for
    paths].

    To show that $A$ satisfies singleton induction, take the distinguished
    element to be $c ofType A$. Let $B$ be a
    #link("note://b05d0e2e-b6ab-45ab-9277-9559f4ee5e1f")[type family] over
    $A$. We must construct a function
    $
        induction_(s)^(c) ofType B(c) -> (piType(x, A) B(x))
    $
    and show that it is a
    #link("note://32c2ca55-63ba-411b-9052-676a51fd16a1")[section] of the
    #link("note://ac0a22e1-3510-4129-ab02-d0f95da4a48c")[evaluation map]
    $
        evaluate_(c) ofType (piType(x, A) B(x)) -> B(c).
    $

    Given $y ofType B(c)$ and $x ofType A$, the contraction provides a path
    $C(x) ofType c =
    x$. #link("note://1229c654-047b-4517-9f4c-df4c03224d02")[Tranporting] $y$
    along this path yields an element of $B(x)$. Accordingly, define
    $
        induction_(s)^(c)(y, x) := tr_(B)(C(x), y).
    $

    To verify the section condition, we must construct a path
    $
        tr_(B)(C(c), y) = y
    $
    for each $y ofType B(c)$. Using our assumed path $C(c) = refl_(c)$ and
    #link("note://1229c654-047b-4517-9f4c-df4c03224d02")[by definition of the
    transport operation], we obtain
    $
        tr_(B)(C(c), y) = tr_(B)(refl_(c), y) dot(eq) y.
    $

    ($<==$) Conversely, assume that $A$ satisfies singleton induction, and let
    $a ofType A$ be the distinguished element. Apply singleton induction to the
    family $P ofType A -> cal(U)$ given by $P(x) := (a = x)$. We obtain a
    function
    $
        induction_(s)^(a) ofType a = a -> (piType(x, A) a = x).
    $
    Applying this to $refl_(a)$ yields
    $
        piType(x, A) a = x,
    $
    which is precisely the same as a contraction with center $a$. Thus, taking
    $a$ as the center of contraction and $C$ as the contraction demonstrates
    that $A$ is contractible.
]

```agda
isContractible→isSingleton :
  {i j : Level} {A : Type i} →
  IsContractible A → IsSingleton {j = j} A
isContractible→isSingleton {_} {j} {A} (pair c C) =
  pair c (isContractible→isSingleton' C' p)
  where
  C' : (x : A) → c ＝ x
  C' x = ((C c) ⁻¹) ∙ (C x)

  p : C' c ＝ reflexive
  p = ⁻¹-inverseˡ $ C c

  isContractible→isSingleton' :
    (C : (x : A) → c ＝ x)
    (p : C c ＝ reflexive)
    (B : A → Type j) →
    Section (_|>_ {A = A} {B = B} c)
  isContractible→isSingleton' C p B = pair induction H
    where
    induction : B c → ((x : A) → B x)
    induction y x = transport B (C x) y 

    H : (y : B c) → induction y c ＝ y
    H y = pathAction (λ q → transport B q y) p

isSingleton→isContractible :
  {i j : Level} {A : Type i} →
  IsSingleton {j = i ⊔ j} A → IsContractible A
isSingleton→isContractible {j = j} (pair a p) with p (λ x → Lift j (a ＝ x))
... | (pair induction _) = pair a (lower ∘ (induction (lift reflexive)))

isContractible↔isSingleton :
  {i j : Level} {A : Type i} →
  IsContractible A ↔ IsSingleton {j = i ⊔ j} A 
isContractible↔isSingleton {i} {j} {A} =
  pair isContractible→isSingleton (isSingleton→isContractible {j = j})
```

= The fundamental theorem of identity types <note:47c2a4df-e0c1-49a6-8ce8-feae75d30105>
 
#theorem(
    supplement: [The fundamental theorem of identity types; #cite_link(<rijke2025>, "Rijke 2025, thm. 11.1.2")]
)[
    Let $A$ be a type with an element $a ofType A$, and let $B$ be a
    #link("note://b05d0e2e-b6ab-45ab-9277-9559f4ee5e1f")[type family] over $A$
    equipped with an element $b ofType B(a)$. Furthermore, consider a family of
    maps
    $
        f ofType piType(x, A) (a = x) -> B(x).
    $
    Then the following are equivalent:

    1. The family of maps $f$ is a
       #link("note://60d115f9-9bef-47af-916a-1a60ea0b3456")[family of
       equivalences].
    2. The #link("note://ae098784-7572-4d29-b548-a2db9b6d004a")[total space]
       $
           sigmaType(x, A) B(x)
       $
       is #link("note://f817901c-750e-4575-a259-d83730424ade")[contractible].
    3. The family $B$ equipped with $b ofType B$ is an
       #link("note://f349b4cc-b6bb-433a-be57-9f2a3d9d8757")[identity system].
]
#proof[

    First we show that (1) and (2) are logically equivalent. By
    #link("note://1e59ed56-2044-4945-8e7e-c97df7680b26")[Theorem 45], the family
    of maps $f$ is a family of equivalences if and only if the
    #link("note://6561eded-451d-46bb-8194-c64a0acf904e")[induced map on total
    spaces]

    $
        total(f) ofType sigmaType(x, A) (a = x) -> sigmaType(x, A) B(x)
    $
    is an #link("note://32c2ca55-63ba-411b-9052-676a51fd16a1")[equivalence].
    #link("note://0505440a-b3cf-41ad-b847-df4a87400d7a")[Theorem 46] shows that
    the type $sigmaType(x, A) (a = x)$ is contractible. Since equivalences
    preserve contractibility by
    #link("note://41aea79b-658b-464d-b9c4-0326602aa2db")[Lemma 42], it follows
    that $total(f)$ is an equivalence if and only if $sigmaType(x, A) B(x)$ is
    contractible. This establishes the logical equivalence of (1) and (2).

    // Next, we show that (2) and (3) are logically equivalent. A type is
    // contractible if and only if it satisfies
    // #link("note://2a65336f-3db1-411e-869f-9c87a18d408a")[singleton induction] by
    // #link("note://dc1d2466-8ead-40b1-9924-f60afcefe390")[Theorem 38], so it
    // suffices to show that $sigmaType(x, A) B(x)$ satisfies singleton induction
    // if and only if $(B, b)$ is an identity system. By the definitions of these
    // concepts, it suffices to fix a type family $P$ indexed by $u ofType
    // sigmaType(x, A) B(x)$ and show that

    Next, we show that (2) and (3) are logically equivalent. By
    #link("note://dc1d2466-8ead-40b1-9924-f60afcefe390")[Theorem 38], a type is
    contractible if and only if it satisfies
    #link("note://2a65336f-3db1-411e-869f-9c87a18d408a")[singleton
    induction]. Therefore, we can instead show that $sigmaType(x, A) B(x)$
    satisfies singleton induction if and only if $(B, b)$ forms an identity
    system. Unfolding both definitions, this amounts to showing that for every
    type family $P(u)$ indexed by $u ofType sigmaType(x, A) B(x)$, the
    #link("note://ac0a22e1-3510-4129-ab02-d0f95da4a48c")[evaluation map]
    $
        lambda h . h((a, b)) ofType (piType(u, sigmaType(x, A) B(x)) P(u)) -> P((a, b))
    $
    has a #link("note://32c2ca55-63ba-411b-9052-676a51fd16a1")[section] if and only if
    $
        lambda h . h(a, b) ofType (piType(x, A) piType(y, B(x)) P((x, y))) -> P((a, b))
    $
    has a section.

    These two maps fit into a commuting triangle:
    #let currys = $#math.sans("curry")$
    #figure(
        diagram($
            piType(u, sigmaType(x, A) B(x)) P(u) edge("rr", currys, ->) edge("dr", lambda h . h((a, b)), ->, label-side: #right)
                & & piType(x, A) piType(y, B(x)) P((x, y)) edge("dl", lambda h . h(a, b), ->, label-side: #left) \
                & P((a, b))
        $)
    )
    Since #link("note://bc0fb217-3c37-4034-9681-ab3040569951")[`curry`] admits a
    section by #link("note://89c0b826-88d2-47b9-9c24-5cd1468c03ee")[Lemma 47],
    it follows by #link("note://b92b0253-66cd-46ff-aaab-8c33541cfd45")[Lemma 48]
    that the left evaluation map has a section if and only if the right map has
    a section.

    This completes the proof.
]

```agda
characterize-＝↔totalIsContractible :
  {i j : Level} {A : Type i} {B : A → Type j}
  (a : A)
  (f : (x : A) → a ＝ x → B x) →
  ((x : A) → IsEquivalence $ f x) ↔ IsContractible (Σ A B)
characterize-＝↔totalIsContractible {_} {_} {A} {B} a f = q ∘↔ p
  where
  p : ((x : A) → IsEquivalence $ f x) ↔
      IsEquivalence (total f)
  p = familyOfEquivalences↔totalIsEquivalence f
                                              
  q : IsEquivalence (total f) ↔ IsContractible (Σ A B)
  q = pair r s
    where
    r : IsEquivalence (total f) → IsContractible (Σ A B)
    r = (flip $ isEquivalence→isContractible→isContractible₁ (total f))
        (endpointPathContractible a)

    s : IsContractible (Σ A B) → IsEquivalence (total f)
    s = isContractible→isContractible→isEquivalence
        (total f) (endpointPathContractible a)

totalIsContractible↔identitySystem :
  {i j k : Level} {A : Type i} {B : A → Type j} →
  IsContractible (Σ A B) ↔
  Σ A (λ a → Σ (B a) (λ b → IdentitySystem {k = i ⊔ j ⊔ k} A a B b))
totalIsContractible↔identitySystem {i} {j} {k} {A} {B} = q' ∘↔ p
  where
  p : IsContractible (Σ A B) ↔ IsSingleton {j = i ⊔ j ⊔ k} (Σ A B)
  p = isContractible↔isSingleton {j = k}

  q : (a : A) (b : B a) (P : Σ A B → Type (i ⊔ j ⊔ k)) →
      Section (_|>_ {B = P} (pair a b)) ↔
      Section (λ (h : (x : A) (y : B x) → P $ pair x y) → h a b)
  q a b P = pair s t
    where
    r : (_|>_ {B = P} (pair a b)) ∼
        (λ (h : (x : A) (y : B x) → P $ pair x y) → h a b) ∘ curry
    r f = reflexive

    s : Section (_|>_ {B = P} (pair a b)) →
        Section (λ h → h a b)
    s = sectionTop→left→right
          (_|>_ (pair a b)) (λ h → h a b) curry
          r (pair uncurry' (curryUncurry'Section {C = P}))

    t : Section (λ h → h a b) →
        Section (_|>_ {B = P} (pair a b))
    t = sectionTop→right→left
          (_|>_ (pair a b)) (λ h → h a b) curry
          r (pair uncurry' (curryUncurry'Section {C = P}))

  q' : IsSingleton {j = i ⊔ j ⊔ k} (Σ A B) ↔
       Σ A (λ a → Σ (B a) (λ b → IdentitySystem {k = i ⊔ j ⊔ k} A a B b))
  q' = pair r s
    where
    r : IsSingleton (Σ A B) →
        Σ A (λ a → Σ (B a) (λ b → IdentitySystem A a B b))
    r (pair (pair a b) s) = pair a (pair b r')
      where
      r' : IdentitySystem A a B b
      r' P = project₁ (q a b (uncurry P)) (s (uncurry P))

    s : Σ A (λ a → Σ (B a) (λ b → IdentitySystem A a B b)) →
        IsSingleton (Σ A B)
    s (pair a (pair b t)) = pair (pair a b) s'
      where
      s' : (P : Σ A B → Type (i ⊔ j ⊔ k)) → Section (_|>_ {B = P} (pair a b))
      s' P = project₂ (q a b P) (t (curry P))
```
