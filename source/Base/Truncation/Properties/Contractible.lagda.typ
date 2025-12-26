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
open import Base.Identity.Core hiding (induction)
open import Base.Identity.Definitions
open import Base.Identity.Properties
open import Data.Sigma.Core hiding (induction)
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

isContractible↔isSingelton :
  {i j : Level} {A : Type i} →
  IsContractible A ↔ IsSingleton {j = i ⊔ j} A 
isContractible↔isSingelton {i} {j} {A} =
  pair isContractible→isSingleton (isSingleton→isContractible {j = j})
```
