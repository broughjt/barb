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
open import Base.Identity.Core as Identity hiding (induction)
open import Base.Identity.Definitions
open import Base.Identity.Properties
open import Base.Identity.IdentitySystem
open import Data.Sigma.Core as Sigma hiding (induction)
open import Data.Sigma.Definitions
open import Data.Sigma.Properties.Equivalence
open import Data.Sigma.Properties.Identity
open import Data.Sigma.Properties.Truncation
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

= Identity system if and only if total space satisfies singleton induction <note:36a008be-6519-4e37-b4d9-0ce4f9725879>
 
#theorem(
    label: "61"
)[
    Let $B$ be a #link("note://b05d0e2e-b6ab-45ab-9277-9559f4ee5e1f")[type
    family] over a type $A$. Then the following are
    #link("note://27061ddb-2091-46c1-8752-21db2ab57f44")[equivalent]:

    1. There are elements $a ofType A$ and $b ofType B(a)$ such that the family
       $B$ equipped with $b$ forms an
       #link("note://f349b4cc-b6bb-433a-be57-9f2a3d9d8757")[identity system] on
       $A$ at $a$.

    2. The #link("note://ae098784-7572-4d29-b548-a2db9b6d004a")[total space]
       $sigmaType(x, A) B(x)$ satisfies
       #link("note://2a65336f-3db1-411e-869f-9c87a18d408a")[singleton
       induction].
]
#proof[
    Unfolding the definitions of an
    #link("note://f349b4cc-b6bb-433a-be57-9f2a3d9d8757")[identity system] and
    #link("note://2a65336f-3db1-411e-869f-9c87a18d408a")[singleton induction],
    this amounts to showing that for every type family $P(u)$ indexed by $u
    ofType sigmaType(x, A) B(x)$,
    #link("note://f349b4cc-b6bb-433a-be57-9f2a3d9d8757")[the map]

    $
        lambda h . h(a, b) ofType (piType(x, A) piType(y, B(x)) P((x, y))) -> P((a, b))
    $

    has a #link("note://32c2ca55-63ba-411b-9052-676a51fd16a1")[section] if and
    only if the #link("note://ac0a22e1-3510-4129-ab02-d0f95da4a48c")[evaluation
    map]
    $
        lambda h . h((a, b)) ofType (piType(u, sigmaType(x, A) B(x)) P(u)) -> P((a, b))
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
    a section. This completes the proof.
]

I didn't come up with this proof entirely on my own. I peeked at the diagram in
the proof of the fundamental theorem of identity types given in
#cite(<rijke2025>, form: "prose", supplement: "thm. 11.2.2"). After drawing it
out on my own, I was able to come up with the rest of the argument, but I
probably would have needed to spend a lot more time thinking to come up with the
diagram on my own.

Both this theorem statement and its proof were part of my
#link("note://11444574-89ee-44aa-be94-dbd3591cca2c")[original statement of the
fundamental theorem of identity types]. However, I later came to believe that
the theorem as stated was a bit misleading, and so
#link("note://47c2a4df-e0c1-49a6-8ce8-feae75d30105")[I updated it]. The
motivation for the change is described both in the commentary for the
#link("note://47c2a4df-e0c1-49a6-8ce8-feae75d30105")[new version], and in the
note #link("note://521256a1-2e0e-4eb3-9c10-4ec2938cebfa")[On the quantifiers in
the statement of the fundamental theorem of identity types]. The new version
also describes why I decided to move this characterization using
#link("note://f349b4cc-b6bb-433a-be57-9f2a3d9d8757")[identity systems] to a
separate theorem.

```agda
identitySystem↔totalIsSingleton :
  {i j k : Level} {A : Type i} {B : A → Type j} →
  Σ A (λ a → Σ (B a) (λ b → IdentitySystem {k = i ⊔ j ⊔ k} A a B b)) ↔
  IsSingleton {j = i ⊔ j ⊔ k} (Σ A B)
identitySystem↔totalIsSingleton {i} {j} {k} {A} {B} = q'
  where
  q : (a : A) (b : B a) (P : Σ A B → Type (i ⊔ j ⊔ k)) →
      Section (λ (h : (x : A) (y : B x) → P $ pair x y) → h a b) ↔
      Section (_|>_ {B = P} (pair a b))
  q a b P =
    pair s t
    where
    r : (_|>_ {B = P} (pair a b)) ∼
        (λ (h : (x : A) (y : B x) → P $ pair x y) → h a b) ∘ curry
    r f = reflexive

    s : Section (λ h → h a b) →
        Section (_|>_ {B = P} (pair a b))
    s = sectionTop→right→left
          (_|>_ (pair a b)) (λ h → h a b) curry
          r (pair uncurry' (curryUncurry'Section {C = P}))

    t : Section (_|>_ {B = P} (pair a b)) →
        Section (λ h → h a b)
    t = sectionTop→left→right
          (_|>_ (pair a b)) (λ h → h a b) curry
          r (pair uncurry' (curryUncurry'Section {C = P}))

  q' : Σ A (λ a → Σ (B a) (λ b → IdentitySystem {k = i ⊔ j ⊔ k} A a B b)) ↔
       IsSingleton {j = i ⊔ j ⊔ k} (Σ A B)
  q' = pair r s
    where
    r : Σ A (λ a → Σ (B a) (λ b → IdentitySystem A a B b)) →
        IsSingleton (Σ A B)
    r (pair a (pair b t)) = pair (pair a b) r'
      where
      r' : (P : Σ A B → Type (i ⊔ j ⊔ k)) → Section (_|>_ {B = P} (pair a b))
      r' P = project₁ (q a b P) $ t (curry P)

    s : IsSingleton (Σ A B) →
        Σ A (λ a → Σ (B a) (λ b → IdentitySystem A a B b))
    s (pair (pair a b) s) = pair a (pair b s')
      where
      s' : IdentitySystem A a B b
      s' P = project₂ (q a b (uncurry P)) $ (s (uncurry P))

identitySystem→totalIsSingleton :
  {i j k : Level} {A : Type i} {B : A → Type j} →
  Σ A (λ a → Σ (B a) (λ b → IdentitySystem {k = i ⊔ j ⊔ k} A a B b)) →
  IsSingleton {j = i ⊔ j ⊔ k} (Σ A B)
identitySystem→totalIsSingleton {k = k} =
  project₁ $ identitySystem↔totalIsSingleton {k = k}

totalIsSingleton→identitySystem :
  {i j k : Level} {A : Type i} {B : A → Type j} →
  IsSingleton {j = i ⊔ j ⊔ k} (Σ A B) →
  Σ A (λ a → Σ (B a) (λ b → IdentitySystem {k = i ⊔ j ⊔ k} A a B b))
totalIsSingleton→identitySystem {k = k} =
  project₂ $ identitySystem↔totalIsSingleton {k = k}

identitySystem↔totalIsContractible :
  {i j k : Level} {A : Type i} {B : A → Type j} →
  Σ A (λ a → Σ (B a) (λ b → IdentitySystem {k = i ⊔ j ⊔ k} A a B b)) ↔
  IsContractible (Σ A B)
identitySystem↔totalIsContractible {i} {j} {k} {A} {B} =
  swap (isContractible↔isSingleton {j = i ⊔ j ⊔ k}) ∘↔
  identitySystem↔totalIsSingleton {k = i ⊔ j ⊔ k}

totalIsContractible→identitySystem :
  {i j k : Level} {A : Type i} {B : A → Type j} →
  IsContractible (Σ A B) →
  Σ A (λ a → Σ (B a) (λ b → IdentitySystem {k = i ⊔ j ⊔ k} A a B b))
totalIsContractible→identitySystem {i} {j} {k} =
  project₂ $ identitySystem↔totalIsContractible {k = i ⊔ j ⊔ k}

identitySystem→totalIsContractible :
  {i j k : Level} {A : Type i} {B : A → Type j} →
  Σ A (λ a → Σ (B a) (λ b → IdentitySystem {k = i ⊔ j ⊔ k} A a B b)) →
  IsContractible (Σ A B)
identitySystem→totalIsContractible {i} {j} {k} =
  project₁ $ identitySystem↔totalIsContractible {k = i ⊔ j ⊔ k}

identitySystem→totalIsContractible' : 
  {i j k : Level} {A : Type i} {B : A → Type j}
  (a : A) (b : B a) →
  IdentitySystem {k = i ⊔ j ⊔ k} A a B b →
  IsContractible (Σ A B)
identitySystem→totalIsContractible' {i} {j} {k} {A} {B} a b p =
  identitySystem→totalIsContractible {k = k} (pair a (pair b p))
```

= If the total space satisfies singleton induction then family forms an identity system for any indices <note:2f4439bc-37ff-476b-a989-74e1ae18d0ff>
 
#corollary[
    Let $B$ a #link("note://b05d0e2e-b6ab-45ab-9277-9559f4ee5e1f")[type family]
    over a type $A$. If the
    #link("note://ae098784-7572-4d29-b548-a2db9b6d004a")[total space]
    $
        sigmaType(x, A) B(x)
    $
    is #link("note://f817901c-750e-4575-a259-d83730424ade")[contractible] then,
    for any $a ofType A$ and $b ofType B(a)$, the family $B$ equipped with $b$
    forms an #link("note://f349b4cc-b6bb-433a-be57-9f2a3d9d8757")[identity
    system] over $A$ at $a$.
]
#proof[
    Suppose the total space
    $
        sigmaType(x, A) B(x)
    $
    is #link("note://f817901c-750e-4575-a259-d83730424ade")[contractible] with
    #link("note://f817901c-750e-4575-a259-d83730424ade")[center] $(a', b')$. By
    #link("note://dc1d2466-8ead-40b1-9924-f60afcefe390")[Theorem 38], a type is
    contractible if and only if it satisfies
    #link("note://2a65336f-3db1-411e-869f-9c87a18d408a")[singleton
    induction]. Hence
    $
        sigmaType(x, A) B(x)
    $
    satisfies singleton induction, and then by
    #link("note://36a008be-6519-4e37-b4d9-0ce4f9725879")[Theorem 61] the family
    $B$ equipped with $b'$ forms an
    #link("note://f349b4cc-b6bb-433a-be57-9f2a3d9d8757")[identity system] on $A$
    at $a'$.

    Now let $a ofType A$ and $b ofType B(a)$ be arbitrary. Since the total space
    is contractible, there is a path
    $
        (a', b') = (a, b).
    $
    #link("note://1229c654-047b-4517-9f4c-df4c03224d02")[Transporting] the
    identity system along $p$ shows that $B$ equipped with $b$ is an identity
    system on $A$ at $a$.
]

```agda
totalIsContractible→identitySystem' : 
  {i j k : Level} {A : Type i} {B : A → Type j}
  (p : IsContractible (Σ A B))
  (a : A) (b : B a) →
  IdentitySystem {k = i ⊔ j ⊔ k} A a B b
totalIsContractible→identitySystem' {i} {j} {k} {A} {B}
  p@(pair (pair a' b') C) a b =
  transport
    (λ ?u → IdentitySystem {k = i ⊔ j ⊔ k} A (project₁ ?u) B (project₂ ?u))
    {x = pair a' b'} {y = pair a b}
    r (project₂ $ project₂ q)
  where
  q : Σ A (λ a' → Σ (B a') (λ b' → (IdentitySystem A a' B b')))
  q = totalIsContractible→identitySystem {k = k} p

  r : pair a' b' ＝ pair a b
  r = project₂ p $ pair a b
```

= The fundamental theorem of identity types (version 2; latest) <note:47c2a4df-e0c1-49a6-8ce8-feae75d30105>
 
#theorem(
    supplement: [The fundamental theorem of identity types; #cite_link(<rijke2025>, "Rijke 2025, thm. 11.1.2")]
)[
    Let $B$ be a #link("note://b05d0e2e-b6ab-45ab-9277-9559f4ee5e1f")[type
    family] over a type $A$.

    If the #link("note://ae098784-7572-4d29-b548-a2db9b6d004a")[total space]
    $
        sigmaType(x, A) B(x)
    $
    is #link("note://f817901c-750e-4575-a259-d83730424ade")[contractible], then
    for any element $a ofType A$ and any family of maps
    $
        f ofType piType(x, A) a = x -> B(x),
    $
    the family $f$ is a
    #link("note://60d115f9-9bef-47af-916a-1a60ea0b3456")[family of
    equivalences].

    On the other hand, if there exists an element $a ofType A$ and a family of
    equivalences
    $
        f ofType piType(x, A) a = x -> B(x),
    $
    then the total space
    $
        sigmaType(x, A) B(x)
    $
    is contractible.
]
#proof[
    Suppose that the #link("note://ae098784-7572-4d29-b548-a2db9b6d004a")[total
    space]
    $
        sigmaType(x, A) B(x)
    $
    is #link("note://f817901c-750e-4575-a259-d83730424ade")[contractible]. Let $a ofType A$ and let $
        f ofType piType(x, A) a = x -> B(x)
    $
    be any family of maps. By
    #link("note://1e59ed56-2044-4945-8e7e-c97df7680b26")[Theorem 45], the family
    $f$ is a #link("note://60d115f9-9bef-47af-916a-1a60ea0b3456")[family of
    equivalences] if and only if the
    #link("note://6561eded-451d-46bb-8194-c64a0acf904e")[induced map on total
    spaces]
    $
        total(f) ofType sigmaType(x, A) a = x -> sigmaType(x, A) B(x)
    $
    is an #link("note://32c2ca55-63ba-411b-9052-676a51fd16a1")[equivalence]. By
    #link("note://0505440a-b3cf-41ad-b847-df4a87400d7a")[Theorem 46], the type
    $sigmaType(x, A) a = x$ of endpoint-path pairs is contractible. Since
    equivalences preserve contractibility
    (#link("note://41aea79b-658b-464d-b9c4-0326602aa2db")[Lemma 42]), and since
    $sigmaType(x, A) B(x)$ is contractible by assumption, it follows that
    $total(f)$ is an equivalence, and hence $f$ is a family of equivalences.

    Now suppose there exists an element $a ofType A$ and a family of maps
    $
        f ofType piType(x, A) a = x -> B(x)
    $
    which is a family of equivalences. By
    #link("note://1e59ed56-2044-4945-8e7e-c97df7680b26")[Theorem 45], the
    induced map on total spaces
    $
        total(f) ofType sigmaType(x, A) a = x -> sigmaType(x, A) B(x)
    $
    is an equivalence. By
    #link("note://0505440a-b3cf-41ad-b847-df4a87400d7a")[Theorem 46], the type
    $sigmaType(x, A) a = x$ is contractible. Since equivalences preserve
    contractibility (#link("note://41aea79b-658b-464d-b9c4-0326602aa2db")[Lemma
    42]), it follows that $sigmaType(x, A) B(x)$ is contractible.
]

This is the second version of this note, the previous version is
#link("note://11444574-89ee-44aa-be94-dbd3591cca2c")[here]. While trying to
understand the structure identity principle @rijke2025[thm. 11.6.2], I realized
that the manner in which the fundamenal theorem of identity types is stated in
Rijke---as a symmetric
#link("note://27061ddb-2091-46c1-8752-21db2ab57f44")[logical equivalence]---is
somewhat misleading. The note
#link("note://521256a1-2e0e-4eb3-9c10-4ec2938cebfa")[On the quantifiers in the
statement of the fundamental theorem of identity types] explains this issue and
the motivation for the change in detail.

The result is that the original logical equivalence has been split into two
separate statements, in order to make the difference between universal and
existential quantification in the two directions explicit.

I have also moved the characterization using
#link("note://f349b4cc-b6bb-433a-be57-9f2a3d9d8757")[identity systems] to a
separate theorem (see
#link("note://36a008be-6519-4e37-b4d9-0ce4f9725879")[Theorem 61]).  This is
partly because I think it is an interesting statement in its own right when
phrased entirely using
#link("note://2a65336f-3db1-411e-869f-9c87a18d408a")[singleton induction] rather
than contractibility, and partly because, once the original equivalence was
split into two individual statements, it felt conceptually and organizationally
cleaner not to bundle yet another pair of statements into the same theorem.

```agda
characterize-＝→totalIsContractible :
  {i j : Level} {A : Type i} {B : A → Type j}
  (a : A) (f : (x : A) → a ＝ x → B x) →
  ((x : A) → IsEquivalence $ f x) →
  IsContractible (Σ A B)
characterize-＝→totalIsContractible {_} {_} {A} {B} a f p =
  r
  where
  q : IsEquivalence $ total f
  q = familyOfEquivalences→totalIsEquivalence f p

  r : IsContractible (Σ A B)
  r = isEquivalence→isContractible→isContractible₁
        (total f)
        q
        (endpointPathContractible a)

totalIsContractible→characterize-＝ : 
  {i j : Level} {A : Type i} {B : A → Type j} →
  IsContractible (Σ A B) →
  (a : A) (f : (x : A) → a ＝ x → B x) →
  ((x : A) → IsEquivalence $ f x)
totalIsContractible→characterize-＝ {A = A} p a f =
  r
  where
  q : IsEquivalence $ total f
  q = isContractible→isContractible→isEquivalence
        (total f)
        (endpointPathContractible a)
        p
  
  r : (x : A) → IsEquivalence $ f x
  r = totalIsEquivalence→familyOfEquivalences f q
```

= Specialization of the fundamental theorem of identity types to path induction <note:b0837fb6-871b-4d44-8a72-d080ee36b590>

#corollary(label: "62")[
    Let $B$ be a #link("note://b05d0e2e-b6ab-45ab-9277-9559f4ee5e1f")[type
    family] over a type $A$.

    If the #link("note://ae098784-7572-4d29-b548-a2db9b6d004a")[total space]
    $
        sigmaType(x, A) B(x)
    $
    is #link("note://f817901c-750e-4575-a259-d83730424ade")[contractible], then
    for any $a ofType A$ and any $b ofType B(a)$ the family of maps
    $
        induction_(=)^(a)(b) ofType piType(x, A) a = x -> B(x) 
    $
    given by #link("note://261490cb-2887-4247-9a83-7f674e3c9651")[path
    induction] based at $a$ is a
    #link("note://60d115f9-9bef-47af-916a-1a60ea0b3456")[family of
    equivalences].

    On the other hand, if there exist $a ofType A$ and $b ofType B(a)$ such that
    $
        induction_(=)^(a)(b) ofType piType(x, A) a = x -> B(x) 
    $
    is a family of equivalences, then the total space
    $
        sigmaType(x, A) B(x)
    $
    is contractible.
]
#proof[
    Apply both parts of the
    #link("note://47c2a4df-e0c1-49a6-8ce8-feae75d30105")[fundamental theorem of
    identity types] to the family of maps given
    #link("note://261490cb-2887-4247-9a83-7f674e3c9651")[path induction].
]

```agda
totalIsContractible→＝-induction-familyOfEquivalences : 
  {i j : Level} {A : Type i} {B : A → Type j}
  (p : IsContractible (Σ A B))
  (a : A) (b : B a) →
  ((x : A) → IsEquivalence (Identity.induction {a = a} {P = λ x p → B x} b x))
totalIsContractible→＝-induction-familyOfEquivalences {B = B} p a b =
  totalIsContractible→characterize-＝
    p a
    (Identity.induction {a = a} {P = λ x p → B x} b)

＝-induction-familyOfEquivalences→totalIsContractible :
  {i j : Level} {A : Type i} {B : A → Type j}
  (a : A) (b : B a) →
  ((x : A) → IsEquivalence (Identity.induction {a = a} {P = λ x p → B x} b x)) →
  IsContractible (Σ A B)
＝-induction-familyOfEquivalences→totalIsContractible {B = B} a b p =
  characterize-＝→totalIsContractible
    a (Identity.induction {a = a} {P = λ x p → B x} b) p
```

= Fundamental theorem of identity types as a logical equivalence with existential quantification <note:6a109597-bec9-4512-8fad-64fa6e539512>
 
#corollary(label: "63")[
    Let $B$ be a #link("note://b05d0e2e-b6ab-45ab-9277-9559f4ee5e1f")[type
    family] over $A$. Then the following are
    #link("note://27061ddb-2091-46c1-8752-21db2ab57f44")[logically equivalent]:

    1. There exists an element $a ofType A$ and a family of maps
       $
           f ofType piType(x, A) a = x -> B(x)
       $
       such that $f$ is a
       #link("note://60d115f9-9bef-47af-916a-1a60ea0b3456")[family of
       equivalences].
    2. The #link("note://ae098784-7572-4d29-b548-a2db9b6d004a")[total space]
       $sigmaType(x, A) B(x)$ is
       #link("note://f817901c-750e-4575-a259-d83730424ade")[contractible].
]
#proof[
    The forward direction ($==>$) is exactly the second part of the
    #link("note://47c2a4df-e0c1-49a6-8ce8-feae75d30105")[fundamental theorem of
    identity types].

    For the reverse direction ($<==$), suppose that $sigmaType(x, A) B(x)$ is
    #link("note://f817901c-750e-4575-a259-d83730424ade")[contractible] with
    #link("note://f817901c-750e-4575-a259-d83730424ade")[center] $(a, b)$. By
    #link("note://b0837fb6-871b-4d44-8a72-d080ee36b590")[Corollary 62], the
    family of maps
    $
        induction_(=)^(a)(b) ofType piType(x, A) a = x -> B(x)
    $
    obtained by #link("note://261490cb-2887-4247-9a83-7f674e3c9651")[path
    induction] on $b$ is a family of equivalences. This exhibits the required
    element $a$ and family of equivalences.
]

```agda
familyOfEquivalences↔totalIsContractible : 
  {i j : Level} {A : Type i} {B : A → Type j} →
  Σ A (λ a →
  Σ (B a)
  (λ b → (x : A) →
    IsEquivalence $ Identity.induction {a = a} {P = λ x p → B x} b x)) ↔
  IsContractible (Σ A B)
familyOfEquivalences↔totalIsContractible {A = A} {B = B} = pair p q
  where
  p : Σ A
      (λ a →
      Σ (B a) (λ b → (x : A) → IsEquivalence $ Identity.induction b x)) →
      IsContractible (Σ A B)
  p (pair a (pair b r)) =
    characterize-＝→totalIsContractible a (Identity.induction b) r

  q : IsContractible (Σ A B) →
      Σ A
      (λ a →
      Σ (B a) (λ b → (x : A) → IsEquivalence $ Identity.induction b x))
  q r@(pair (pair a b) C) =
    pair
      a
      (pair b (totalIsContractible→characterize-＝ r a (Identity.induction b)))
```

= Maps in and out of contractible types are homotopic to constant maps <note:6c0f7999-0810-49f8-92f3-259ad996a7f1>
 
#lemma[
    Let $A$ be a
    #link("note://f817901c-750e-4575-a259-d83730424ade")[contractible type] with
    #link("note://f817901c-750e-4575-a259-d83730424ade")[center]
    $c ofType A$. For all maps $f ofType A -> B$, there is a
    #link("note://3cb1b8ca-2a77-4c8a-b726-ed8f10dfd208")[homotopy]
    $
        constant_(f(c)) ~ f.
    $
    Similarly, for all maps $g ofType B -> A$, there is a homotopy
    $
        constant_(c) ~ g.
    $
]
#proof[
    Let $A$ be contractible with center $c ofType A$ and contraction $C$.

    For $f ofType A -> B$, applying $f$ to the
    #link("note://261490cb-2887-4247-9a83-7f674e3c9651")[path] $C(x) ofType c =
    x$ yields a path $f(c) = f(x)$. These paths determine the required homotopy,
    since $constant_(f(c))(x) dot(eq) f(c)$
    #link("note://11168612-1fca-405d-b3c5-2ecb0ece3521")[by definition].

    Similarly, for $g ofType B -> A$, the contraction yields for each $y ofType
    B$ a path
    $
        C(g(y)) ofType c = g(y)
    $
    exhibiting a homotopy $constant_(c) ~ g$.
]

See #link("note://11168612-1fca-405d-b3c5-2ecb0ece3521")[Constant function].

```agda
contractible→-homotopyConstant :
  {i j : Level} {A : Type i} {B : Type j} →
  (p : IsContractible A)
  (f : A → B) →
  constant (f $ project₁ p) ∼ f
contractible→-homotopyConstant (pair c C) f x = pathAction f (C x)

contractible→-homotopyConstant' :
  {i j : Level} {A : Type i} {B : Type j} →
  (p : IsContractible A)
  (c : A)
  (f : A → B) →
  constant (f $ c) ∼ f
contractible→-homotopyConstant' (pair c' C) c f x =
  pathAction f (C c) ⁻¹ ∙ contractible→-homotopyConstant (pair c' C) f x

→contractible-homotopyConstant :
  {i j : Level} {A : Type i} {B : Type j} →
  (p : IsContractible A)
  (g : B → A) →
  constant (project₁ p) ∼ g
→contractible-homotopyConstant (pair c C) g y = C $ g y 

→contractible-homotopyConstant' :
  {i j : Level} {A : Type i} {B : Type j} →
  (p : IsContractible A)
  (c : A)
  (g : B → A) →
  constant c ∼ g
→contractible-homotopyConstant' (pair c' C) c g y =
  (C c) ⁻¹ ∙ →contractible-homotopyConstant (pair c' C) g y
```

= Structure identity principle <note:c8ded883-fe70-482b-804b-157512315c1f>

#theorem(
    supplement: cite_link(<rijke2025>, "Structure identity principle; Rijke 2025, thm. 11.6.2")
)[
    Consider a #link("note://b05d0e2e-b6ab-45ab-9277-9559f4ee5e1f")[type family]
    $B$ over a type $A$. Let
    $
        C ofType A -> cal(U), quad D ofType piType(x, A) B(x) -> C(x) -> cal(V)
    $
    be auxiliary type families. Suppose:

    1. The #link("note://ae098784-7572-4d29-b548-a2db9b6d004a")[total space]
       $sigmaType(x, A) C(x)$ is
       #link("note://f817901c-750e-4575-a259-d83730424ade")[contractible] with
       #link("note://f817901c-750e-4575-a259-d83730424ade")[center] $(a, c)$.
    2. The total space $sigmaType(y, B(a)) D(a, y, c)$ is contractible.

    Then for any $(a, b) ofType sigmaType(x, A) B(x)$ and any family of functions
    $
        f ofType piType((x, y), sigmaType(x, A) B(x)) (a, b) = (x, y) -> sigmaType(z, C(x)) D(x, y, z)
    $
    the family $f$ is a
    #link("note://60d115f9-9bef-47af-916a-1a60ea0b3456")[family of
    equivalences].
]
#proof[
    We show that the total space
    $
        sigmaType((x, y), sigmaType(x, A) B(x)) sigmaType(z, C(x)) D(x, y, z)
    $
    is contractible. Then claim will then follow from the
    #link("note://47c2a4df-e0c1-49a6-8ce8-feae75d30105")[fundamental theorem of
    identity types].

    By interchange law given in
    #link("note://b33026a4-684f-4856-845c-98ca94c51ea8")[Lemma 67], there is an
    #link("note://32c2ca55-63ba-411b-9052-676a51fd16a1")[equivalence]
    $
        sigmaType((x, y), sigmaType(x, A) B(x)) & sigmaType(z, C(x)) D(x, y, z) tilde.eq \
        sigmaType((x, z), sigmaType(x, A) C(x)) & sigmaType(y, B(x)) D(x, y, z).
    $
    By #link("note://9f820c12-c050-423b-ae07-cc1fb0cddd37")[Lemma 68], any
    $Sigma$-type over a contractible base is equivalent to the
    #link("note://85839d30-6530-4e54-a8ba-efd1c8709928")[fiber] over its center
    of contraction. By assumption, the base $sigmaType(x, A) C(x)$ is
    contractible, so there is an equivalence
    $
        sigmaType((x, z), sigmaType(x, A) C(x)) sigmaType(y, B(x)) D(x, y, z) tilde.eq
        sigmaType(y, B(a)) D(a, y, c).
    $
    Since the right-hand side is contractible by assumption and contractibility
    is preserved by equivalence
    (#link("note://41aea79b-658b-464d-b9c4-0326602aa2db")[Lemma 42]), it follows
    that the total space
    $
        sigmaType((x, y), sigmaType(x, A) B(x)) & sigmaType(z, C(x)) D(x, y, z)
    $
    is contractible.

    The claim now follows by applying the
    #link("note://47c2a4df-e0c1-49a6-8ce8-feae75d30105")[fundamental theorem of
    identity types] to this contractible total space.
]

```agda
componentTotalIsContractible→structureTotalIsContractible :
  {i j k l : Level}
  {A : Type i} {B : A → Type j}
  {C : A → Type k} {D : (x : A) → B x → C x → Type l}
  (p : IsContractible (Σ A C)) →
  let u = project₁ p
      a = project₁ u
      c = project₂ u
  in
  IsContractible (Σ (B a) (λ y → D a y c)) →
  IsContractible (Σ (Σ A B)
                    (λ u → Σ (C $ project₁ u)
                    (λ z → D (project₁ u) (project₂ u) z)))
componentTotalIsContractible→structureTotalIsContractible
  {_} {_} {_} {_} {A} {B} {C} {D}
  p@(pair (pair a c) P) q = ω
  where
  φ : IsEquivalence $ interchangeʳ {D = D}
  φ = interchangeʳ-isEquivalence

  ψ : IsEquivalence
        (pair {B = λ v → Σ (B $ project₁ v)
                           (λ y → D (project₁ v) y (project₂ v))} (pair a c))
  ψ = baseIsContractible→pairIsEquivalence p

  ω : IsContractible
        (Σ (Σ A B)
           (λ u → Σ (C $ project₁ u) (D (project₁ u) (project₂ u))))
  ω = isEquivalence→isContractible→isContractible₁
        (interchangeʳ ∘ pair (pair a c))
        (isEquivalenceCompose interchangeʳ (pair (pair a c)) φ ψ)
        q

componentTotalIsContractible→structureTotalIsContractible' :
  {i j k l : Level}
  {A : Type i} {B : A → Type j}
  {C : A → Type k} {D : (x : A) → B x → C x → Type l}
  (u : Σ A C) →
  IsContractible (Σ A C) →
  let a = project₁ u
      c = project₂ u
  in
  IsContractible (Σ (B a) (λ y → D a y c)) →
  IsContractible (Σ (Σ A B)
                    (λ u → Σ (C $ project₁ u)
                    (λ z → D (project₁ u) (project₂ u) z)))
componentTotalIsContractible→structureTotalIsContractible'
  {_} {_} {_} {_} {A} {B} {C} {D} (pair a c) p@(pair (pair a' c') P) q =
  componentTotalIsContractible→structureTotalIsContractible p q'
  where
  q' : IsContractible (Σ (B a') (λ y → D a' y c'))
  q' = transport (λ ?u → IsContractible
                           (Σ (B $ project₁ ?u)
                              (λ y → D (project₁ ?u) y (project₂ ?u))))
                 ((P $ pair a c) ⁻¹)
                 q

componentTotalIsContractible→characterize-＝-structure :
  {i j k l : Level}
  {A : Type i} {B : A → Type j}
  {C : A → Type k} {D : (x : A) → B x → C x → Type l}
  (p : IsContractible (Σ A C)) →
  let w = project₁ p
      a = project₁ w
      c = project₂ w
  in
  (q : IsContractible (Σ (B a) (λ y → D a y c))) →
  (u : Σ A B) → 
  (f : (v : Σ A B) →
       u ＝ v → Σ (C $ project₁ v) (λ z → D (project₁ v) (project₂ v) z)) →
  ((v : Σ A B) → IsEquivalence $ f v)
componentTotalIsContractible→characterize-＝-structure
  {_} {_} {_} {_} {A} {B} {C} {D} p q u =
  s
  where
  r : IsContractible
        (Σ (Σ A B)
           (λ u₁ → Σ (C $ project₁ u₁) (D (project₁ u₁) (project₂ u₁))))
  r = componentTotalIsContractible→structureTotalIsContractible {D = D} p q

  s : (f : (v : Σ A B) →
           u ＝ v → Σ (C $ project₁ v) (D (project₁ v) (project₂ v))) →
      ((v : Σ A B) → IsEquivalence $ f v)
  s = totalIsContractible→characterize-＝ r u

componentTotalIsContractible→characterize-＝-structure' :
  {i j k l : Level}
  {A : Type i} {B : A → Type j}
  {C : A → Type k} {D : (x : A) → B x → C x → Type l}
  (a : A) (c : C a) →
  IsContractible (Σ A C) →
  IsContractible (Σ (B a) (λ y → D a y c)) →
  (u : Σ A B) → 
  (f : (v : Σ A B) →
       u ＝ v → Σ (C $ project₁ v) (λ z → D (project₁ v) (project₂ v) z)) →
  ((v : Σ A B) → IsEquivalence $ f v)
componentTotalIsContractible→characterize-＝-structure'
  {_} {_} {_} {_} {A} {B} {C} {D} a c p q u =
  s
  where
  r : IsContractible
        (Σ (Σ A B)
           (λ v → Σ (C $ project₁ v) (D (project₁ v) (project₂ v))))
  r = componentTotalIsContractible→structureTotalIsContractible' {D = D}
        (pair a c) p q

  s : (f : (v : Σ A B) →
           u ＝ v → Σ (C $ project₁ v) (D (project₁ v) (project₂ v))) →
      ((v : Σ A B) → IsEquivalence $ f v)
  s = totalIsContractible→characterize-＝ r u
```

= To characterize an identity type, it suffices to give a family of maps out of the identity type equipped with sections <note:7509e68a-5c1a-4ce8-aa53-fce8adc17522>
 
#lemma(
    label: "83",
    supplement: cite_link(<rijke2025>, "Rijke 2025, exer. 11.8(d-e)")
)[
    Let
    $
        f ofType piType(x, A) a = x -> B(x)
    $
    be a family of maps. If there is a family of maps
    $
        g ofType piType(x, A) B(x) -> a = x
    $
    such that $g(x)$ is a
    #link("note://32c2ca55-63ba-411b-9052-676a51fd16a1")[section] of $f(x)$ for
    each $x ofType A$, then $f$ is a
    #link("note://60d115f9-9bef-47af-916a-1a60ea0b3456")[family of
    equivalences].
]
#proof[
    By the #link("note://47c2a4df-e0c1-49a6-8ce8-feae75d30105")[fundamental
    theorem of identity types], to show that $f$ is a family of equivalences it
    suffices to show that the
    #link("note://ae098784-7572-4d29-b548-a2db9b6d004a")[total space]
    $
        sigmaType(x, A) B(x)
    $
    is #link("note://f817901c-750e-4575-a259-d83730424ade")[contractible].

    By assumption, for each $x ofType A$, the map $g(x)$ is a section of
    $f(x)$. By #link("note://2957f389-a645-430c-bcb3-efe6f2565b28")[Lemma 81],
    it follows that the
    #link("note://6561eded-451d-46bb-8194-c64a0acf904e")[induced map on total
    spaces]
    $
        total(g) ofType sigmaType(x, A) B(x) -> sigmaType(x, A) a = x
    $
    is a section of
    $
        total(f) ofType sigmaType(x, A) a = x -> sigmaType(x, A) B(x).
    $
    #link("note://608cfcd8-b127-4cde-a4ad-afcb1f38cccd")[Equivalently],
    $total(f)$ is a
    #link("note://32c2ca55-63ba-411b-9052-676a51fd16a1")[retraction] of
    $total(g)$.

    By #link("note://591c6be7-77c3-4215-a126-f27d87c6bd65")[Lemma 82], if a map
    has a retraction, then contractibility of its codomain implies
    contractibility of its domain. Hence it suffices to show that
    $
        sigmaType(x, A) a = x
    $
    is contractible. But the type of endpoint-path pairs is contratible by
    #link("note://0505440a-b3cf-41ad-b847-df4a87400d7a")[Theorem 46]. Therefore
    $sigmaType(x, A) B(x)$ is contractible, and the claim follows.
]

```agda
familyOfRightInverses→characterize-＝ :
  {i j : Level} {A : Type i} {B : A → Type j}
  (a : A)
  (f : (x : A) → a ＝ x → B x)
  (g : (x : A) → B x → a ＝ x) →
  ((x : A) → RightInverse (f x) (g x)) →
  ((x : A) → IsEquivalence $ f x)
familyOfRightInverses→characterize-＝ {_} {_} {A} {B} a f g H =
  totalIsContractible→characterize-＝ q a f
  where
  H' : RightInverse (total f) (total g)
  H' = familyOfRightInverses→totalRightInverse f g H

  p : IsContractible (Σ A (λ x → a ＝ x)) → IsContractible (Σ A B)
  p = retraction→isContractible→isContractible (total g) (total f) H'

  q : IsContractible (Σ A B)
  q = p $ endpointPathContractible a
```

= If the action of a function on paths has a section for each input then the function is an embedding <note:9a00cbde-370e-41f7-88f8-c8bcaff1ba27>
 
#corollary(supplement: cite_link(<rijke2025>, "Rijke 2025, exer. 11.9"))[
    Let $f ofType A -> B$ be a map. If the
    #link("note://7caf7ee0-9e2a-4761-bee9-25cd52820039")[action of $f$ on paths]
    $
        ap_(f) ofType x = y -> f(x) = f(y)
    $
    has a #link("note://32c2ca55-63ba-411b-9052-676a51fd16a1")[section] for each
    $x, y ofType A$, then $f$ is an
    #link("note://cce94748-d9b3-4795-a3d8-c698b6dff9dd")[embedding].
]
#proof[
    Fix $x ofType A$. By assumption, the family of maps
    $
        piType(y, A) x = y -> f(x) = f(y)
    $
    admits a family of sections. By
    #link("note://7509e68a-5c1a-4ce8-aa53-fce8adc17522")[Lemma 83], this family
    is therefore a #link("note://60d115f9-9bef-47af-916a-1a60ea0b3456")[family
    of equivalences]. Since this holds for each $x$, $f$ is an
    #link("note://cce94748-d9b3-4795-a3d8-c698b6dff9dd")[embedding].
]

```agda
familyOfRightInverses→embedding : 
  {i j : Level} {A : Type i} {B : Type j}
  (f : A → B)
  (h : (x y : A) → f x ＝ f y → x ＝ y) →
  ((x y : A) → RightInverse (pathAction f) (h x y)) →
  IsEmbedding f
familyOfRightInverses→embedding f h H x =
  familyOfRightInverses→characterize-＝ x (λ y → pathAction f) (h x) (H x)
```

= If a type is contractible than it has contractible identity types <note:1d8b9cbe-0517-4ca7-840a-d9601bedde8e>

#lemma(
    label: "85",
    supplement: cite_link(<rijke2025>, "Rijke 2025, exer. 10.1")
)[
    If a type $A$ is
    #link("note://f817901c-750e-4575-a259-d83730424ade")[contractible], then for
    all $x, y ofType A$, the
    #link("note://261490cb-2887-4247-9a83-7f674e3c9651")[identity type] $x
    attach(eq, br: A) y$ is also contractible.
]
#proof[
    Let $A$ be a
    #link("note://f817901c-750e-4575-a259-d83730424ade")[contractible type] with
    #link("note://f817901c-750e-4575-a259-d83730424ade")[center of contraction]
    $c ofType A$ and
    #link("note://f817901c-750e-4575-a259-d83730424ade")[contraction] $C ofType
    piType(x, A) c = x$. Fix $x, y ofType A$. We show that the
    #link("note://261490cb-2887-4247-9a83-7f674e3c9651")[identity type] $x
    attach(eq, br: A) y$ is
    #link("note://f817901c-750e-4575-a259-d83730424ade")[contractible].

    Take the #link("note://261490cb-2887-4247-9a83-7f674e3c9651")[path]
    $
        C(x)^(-1) dot.op C(y) ofType x = y.
    $
    as the center of contraction. For the contraction, let $p ofType x = y$. By
    #link("note://261490cb-2887-4247-9a83-7f674e3c9651")[path induction] on $p$,
    we may assume $y$ is $x$ and that $p$ is $refl_(x)$. In this case it
    suffices to construct a path
    $
        C(x)^(-1) dot.op C(x) = refl_(x),
    $
    which we obtain immediately from the
    #link("note://ac149ae0-bd8c-4206-a7bf-eb6e7fa1575e")[left inverse law for
    paths].
]

```agda
isContractible→＝-isContractible :
  {i : Level} {A : Type i}
  (p : IsContractible A) →
  (x y : A) → IsContractible (x ＝ y)
isContractible→＝-isContractible (pair c C) x y = pair d D
  where
  d : x ＝ y
  d = (C x) ⁻¹ ∙ (C y)

  D : (p : x ＝ y) → d ＝ p
  D reflexive = ⁻¹-inverseˡ (C x)
```
