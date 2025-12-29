#import("../../../../../library/template.typ"): *

#show: template

```agda
module Base.Identity.Properties where

open import Base.Family.Definitions
open import Base.Function.Core
open import Base.Function.Definitions as Function hiding (_⁻¹; _∙_)
open import Base.Function.Negation
open import Base.Function.Properties.Equivalence
open import Base.Identity.Core
open import Base.Identity.Definitions
open import Base.Identity.Syntax
open import Base.Truncation.Definitions
open import Base.Universe.Core
open import Data.Sigma.Core
```

= Concatenation on paths is associative <note:f2110298-afe0-4b63-9ef8-923f003cd631>

#lemma(supplement: cite_link(<rijke2025>, [Rijke 2025, def. 5.2.3]))[
    The #link("note://984d4510-34b9-492f-a792-95a19117193e")[concatenation
    operation] on #link("note://261490cb-2887-4247-9a83-7f674e3c9651")[paths] is
    associative. If $A$ is a type, $w, x, y, z ofType A$ are elements, and $p
    ofType x = y$, $q ofType y = z$, $r ofType z = w$ are paths, then there is a
    path
    $
        (p dot.op q) dot.op r = p dot.op (q dot.op r).
    $
]
#proof[
    Fix $x ofType A$. By
    #link("note://261490cb-2887-4247-9a83-7f674e3c9651")[path induction], it is
    sufficient to construct a function
    $
        piType(z, w, A) piType(q, x = z) piType(r, z = w) (refl_(x) dot.op q)
        dot.op r = refl_(x) dot.op (q dot.op r).
    $
    Let $q ofType x = z$ and $r ofType z = w$. By the
    #link("note://261490cb-2887-4247-9a83-7f674e3c9651")[computation rule for
    identity types] and the
    #link("note://984d4510-34b9-492f-a792-95a19117193e")[definition of
    concatenation], we have $refl_x dot.op q dot(eq) q$. It follows that
    $
        (refl_(x) dot.op q) dot.op r dot(eq) q dot.op r.
    $
    Similarly, we also have $refl_(x) dot.op (q dot.op r) dot(eq) q dot.op
    r$. Thus, the left- and right-hand sides of the expression
    $
        (refl_(x) dot.op q) dot.op r = refl_(x) dot.op (q dot.op r)
    $
    are #link("note://a0baf580-5da2-4328-bfbd-202bedf37747")[judgementally
    equal]. Hence, we can take $refl_(q dot.op r)$ to complete the construction.
]

```agda
∙-associative : {i : Level} {A : Type i} {w x y z : A} →
                (p : w ＝ x) (q : x ＝ y) (r : y ＝ z) →
                (p ∙ q) ∙ r ＝ p ∙ (q ∙ r)
∙-associative reflexive q r = reflexive
```

= Concatenation on paths satisfies the left and right unit laws with respect to reflexivity <note:50f1bf11-5d39-455c-a39e-0d560ac5cee5>

#lemma(supplement: cite_link(<rijke2025>, [Rijke 2025, def. 5.2.4]))[
    The #link("note://984d4510-34b9-492f-a792-95a19117193e")[concatenation
    operation] on #link("note://261490cb-2887-4247-9a83-7f674e3c9651")[paths]
    satisfies the left and right unit laws with respect to the reflexivity
    constructor. Given a type $A$ and elements $x, y ofType A$, for all paths $p
    ofType x = y$ we have
    $
        refl_(x) dot.op p & = p, \
        p dot.op refl_(y) & = p.
    $
]
#proof[
    The left unit law holds
    #link("note://a0baf580-5da2-4328-bfbd-202bedf37747")[judgementally] by the
    #link("note://984d4510-34b9-492f-a792-95a19117193e")[definition of
    concatenation] the
    #link("note://261490cb-2887-4247-9a83-7f674e3c9651")[computation law for
    identity types], so take $refl_(p) ofType refl_(x) dot.op p = p$. For the
    right unit law, by #link("note://261490cb-2887-4247-9a83-7f674e3c9651")[path
    induction] on $p$ it suffices to construct an identification
    $
        refl_(x) dot.op refl_(x) = refl_(x).
    $
    This holds judgementally, so we take $refl_(refl_(x)) ofType refl_(x) =
    refl_(x)$.
]

```agda
∙-unitˡ : {i : Level} {A : Type i} {x y : A} →
          (p : x ＝ y) →
          reflexive ∙ p ＝ p
∙-unitˡ p = reflexive

∙-unitʳ : {i : Level} {A : Type i} {x y : A} →
          (p : x ＝ y) →
          p ∙ reflexive ＝ p
∙-unitʳ reflexive = reflexive
```

= Inverse operation on paths satisfies inverse laws <note:ac149ae0-bd8c-4206-a7bf-eb6e7fa1575e>

#lemma(supplement: cite_link(<rijke2025>, [Rijke 2025, def. 5.2.5]))[
    The #link("note://95e3c813-ae44-4341-ac56-286cda078568")[inverse operation]
    on #link("note://261490cb-2887-4247-9a83-7f674e3c9651")[paths] satisfies the
    left and right inverse laws. For any type $A$, elements $x, y ofType A$, and
    path $p ofType x = y$, we have
    $
        p^(-1) dot.op p & = refl_(y), \
        p dot.op p^(-1) & = refl_(x).
    $
]
#proof[
    By #link("note://261490cb-2887-4247-9a83-7f674e3c9651")[path induction] on
    $p$ it suffices to construct paths
    $
        refl_(x)^(-1) dot.op refl_(x) & = refl_(x), \
        refl_(x) dot.op refl_(x)^(-1) & = refl_(x).
    $
    Both equations hold
    #link("note://a0baf580-5da2-4328-bfbd-202bedf37747")[judgementally], since
    we have
    $
        refl_(x)^(-1) dot.op refl_(x) dot(eq) refl_(x) dot.op refl_(x) dot(eq)
        refl_(x)
    $
    and
    $
        refl_(x) dot.op refl_(x)^(-1) dot(eq) refl_(x) dot.op refl_(x) dot(eq)
        refl_(x).
    $
    Therefore, in both cases we take $refl_(refl_(x))$.
]

```agda
⁻¹-inverseˡ : {i : Level} {A : Type i} {x y : A} →
              (p : x ＝ y) →
              p ⁻¹ ∙ p ＝ reflexive
⁻¹-inverseˡ reflexive = reflexive

⁻¹-inverseʳ : {i : Level} {A : Type i} {x y : A} →
              (p : x ＝ y) →
              p ∙ p ⁻¹ ＝ reflexive
⁻¹-inverseʳ reflexive = reflexive
```

= Action on paths respects the identity function <note:e796dbf6-5752-449b-b2b7-420bc93d9679>

#lemma(supplement: cite_link(<rijke2025>, [Rijke 2025, def. 5.3.2]))[
    For all elements $x, y ofType A$ and
    #link("note://261490cb-2887-4247-9a83-7f674e3c9651")[paths] $p ofType x =
    y$, we have
    $
        ap_(id_(A))(p) = p.
    $
]
#proof[
    By #link("note://261490cb-2887-4247-9a83-7f674e3c9651")[path induction], it
    suffices to consider the case $ap_(id_(A))(refl_(x)) = refl_(x)$, which
    holds #link("note://a0baf580-5da2-4328-bfbd-202bedf37747")[judgementally].
]

See #link("note://7caf7ee0-9e2a-4761-bee9-25cd52820039")[Action on paths].

```agda
pathActionIdentity : {i : Level} {A : Type i} {x y : A}
                     (p : x ＝ y) → p ＝ pathAction identity p
pathActionIdentity reflexive = reflexive
```

= Action on paths respects function composition <note:cc4b4cb3-7590-42ae-b468-1a590c448d79>

We can identify the #link("note://261490cb-2887-4247-9a83-7f674e3c9651")[path]
under the successive
#link("note://7caf7ee0-9e2a-4761-bee9-25cd52820039")[actions] of two functions
with the path under the action of their
#link("note://bc9568f6-830b-4b4e-9aab-1808b1127cb0")[composition].

#lemma(supplement: cite_link(<rijke2025>, [Rijke 2025, def. 5.3.1]))[
    Let $x, y ofType A$ be elements of a type $A$. For all paths $p ofType x =
    y$ and maps $f ofType A -> B$, $g ofType B -> C$, we have
    $
        ap_(g)(ap_(f)(p)) = ap_(g compose f)(p).
    $
]
#proof[
    Applying #link("note://261490cb-2887-4247-9a83-7f674e3c9651")[path
    induction], we only need to consider the case
    $
        ap_(g)(ap_(f)(refl_(x))) = ap_(g compose f)(refl_(x)).
    $
    This holds
    #link("note://a0baf580-5da2-4328-bfbd-202bedf37747")[judgementally], since
    we have
    $
        ap_(g)(ap_(f)(refl)) dot(eq) ap_(g)(refl_(f(x))) dot(eq)
        refl_(g(f(x))) dot(eq) ap_(g compose f)(refl_(x)).
    $
]

```agda
pathAction-∘ : {i j k : Level} {A : Type i} {B : Type j} {C : Type k}
                    (f : A → B) (g : B → C) →
                    {x y : A} (p : x ＝ y) →
                    pathAction g (pathAction f p) ＝ pathAction (g ∘ f) p
pathAction-∘ f g reflexive = reflexive
```

= Action on path respects the reflexivity constructor <note:20c0b51f-5bc4-48c5-80be-cab77bcc18c9>

#lemma(supplement: cite_link(<rijke2025>, [Rijke 2025, def. 5.3.2]))[
    For any function $f ofType A -> B$, there is a
    #link("note://261490cb-2887-4247-9a83-7f674e3c9651")[path]
    $
        ap_(f)(refl_(x)) = refl_(f(x)).
    $
]
#proof[
    Observe that $ap_(f)(refl_(x)) dot(eq) refl_(f(x))$
    #link("note://7caf7ee0-9e2a-4761-bee9-25cd52820039")[by definition], then
    take $refl_(refl_(f(x))) ofType refl_(f(x)) = refl_(f(x))$.
]

See #link("note://7caf7ee0-9e2a-4761-bee9-25cd52820039")[Action on paths].

```agda
pathActionReflexive :
  {i j : Level} {A : Type i} {B : Type j}
  (f : A → B) {x : A} →
  pathAction f (reflexive {_} {_} {x}) ＝ reflexive {_} {_} {f x}
pathActionReflexive f = reflexive
```

= Action on paths respects inverse operation on paths <note:810bd01f-04f6-47a4-9de4-d07ee6443bd9>

The #link("note://7caf7ee0-9e2a-4761-bee9-25cd52820039")[action on paths]
respects the #link("note://95e3c813-ae44-4341-ac56-286cda078568")[inverse
operation on paths].

#lemma(supplement: cite_link(<rijke2025>, [Rijke 2025, def. 5.3.2]))[
    Suppose that $f ofType A -> B$ is a function, let $x, y ofType A$, and let
    $p ofType x = y$. Then
    $
        ap_(f)(p^(-1)) = ap_(f)(p)^(-1).
    $
]
#proof[
    By #link("note://261490cb-2887-4247-9a83-7f674e3c9651")[path induction], we
    only need to consider the case
    $
        ap_(f)(refl_(x)^(-1)) = ap_(f)(refl_(x))^(-1).
    $
    Since
    $
        ap_(f)(refl_(x)^(-1)) dot(eq) ap_(f)(refl_(x)) dot(eq) refl_(f(x))
    $
    and
    $
        ap_(f)(refl_(x))^(-1) dot(eq) refl_(f(x))^(-1) dot(eq) refl_(f(x)),
    $
    we can take $refl_(f(x))$ to complete the construction.
]

```agda
pathAction-⁻¹ : {i j : Level} {A : Type i} {B : Type j}
                (f : A → B) {x y : A} (p : x ＝ y) →
                pathAction f (p ⁻¹) ＝ (pathAction f p) ⁻¹
pathAction-⁻¹ f reflexive = reflexive
```

= Action on paths respects concatenation operation on paths <note:e9001b3b-05d3-4703-9f37-ecba27832641>
 
The #link("note://7caf7ee0-9e2a-4761-bee9-25cd52820039")[action on paths]
respects the #link("note://984d4510-34b9-492f-a792-95a19117193e")[concatenation
operation on paths].

#lemma(supplement: cite_link(<rijke2025>, [Rijke 2025, def. 5.3.2]))[
    Suppse that $f ofType A -> B$ is a function, let $x, y, z ofType A$ be
    elements, and let $p ofType x = y$ and $q ofType y = z$ be
    #link("note://261490cb-2887-4247-9a83-7f674e3c9651")[paths]. Then
    $
        ap_(f)(p dot.op q) = ap_(f)(p) dot.op ap_(f)(q).
    $
]
#proof[
    Apply #link("note://261490cb-2887-4247-9a83-7f674e3c9651")[path induction]
    so that we only need to consider the case
    $
        ap_(f)(refl_(x) dot.op q) = ap_(f)(refl_(x)) dot.op ap_(f)(q).
    $
    This holds
    #link("note://a0baf580-5da2-4328-bfbd-202bedf37747")[judgementally], because
    we have
    $
        ap_(f)(refl_(x) dot.op q) dot(eq) ap_(f)(q)
    $
    and
    $
        ap_(f)(refl_(x)) dot.op ap_(f)(q) dot(eq) refl_(f(x)) dot.op ap_(f)(q)
        dot(eq) ap_(f)(q).
    $
    Consequently, we can take $refl_(ap_(f)(q)) ofType ap_(f)(q) = ap_(f)(q)$ to
    complete the construction.
]

```agda
pathAction-∙ : {i j : Level} {A : Type i} {B : Type j}
               (f : A → B) {x y z : A} (p : x ＝ y) (q : y ＝ z) →
               pathAction f (p ∙ q) ＝ (pathAction f p) ∙ (pathAction f q)
pathAction-∙ f reflexive q = reflexive
```

= Endpoint-path pairs are unique <note:536f383d-a59f-4ad3-8c15-82f0a7b9822d>

The following lemma---which shows that endpoint-path
#link("note://ae098784-7572-4d29-b548-a2db9b6d004a")[pairs] are unique---seems
to be the best we can do in terms of stating the sense in which the reflexivity
constructor for the
#link("note://261490cb-2887-4247-9a83-7f674e3c9651")[identity type] is
unique. See #link("note://f74e753e-7683-40ca-bc1d-ce3771645b28")[Best current
attempt at reasoning why only endpoint-path pairs are unique] for discussion.

#lemma(label: "1", supplement: cite_link(<rijke2025>, [Rijke 2025, prop. 5.5.1]))[
    Let $A$ be a type and let $a ofType A$. For all endpoint-path pairs $u
    ofType sigmaType(x, A) a = x$, there is a
    #link("note://261490cb-2887-4247-9a83-7f674e3c9651")[path]
    $
        (a, refl_(a)) = u.
    $
]

#proof[
    Formally, we are trying to construct a function
    $
        piType(u, sigmaType(x, A) a = x) (a, refl_(a)) = u.
    $
    By #link("note://ae098784-7572-4d29-b548-a2db9b6d004a")[$Sigma$-induction],
    it suffices to construct a function
    $
        piType(x, A) piType(p, a = x) (a, refl_(a)) = (x, p).
    $
    In turn, by #link("note://261490cb-2887-4247-9a83-7f674e3c9651")[path
    induction] it suffices provide an identification
    $
        (a, refl_(a)) = (a, refl_(a)),
    $
    so we can take $refl_((a, refl_(a)))$ to complete the proof.
]

Since this is unintuitive to me, I was a bit more explicit in my proof writing
than normal. Specifically, I made the type (logical formula) of the statement
we're proving explicit---something
#link("note://4c786ae8-77b0-4c19-a282-23a8f508b660")[I learned to lean away
from] after reading Newstead's guide on proof writing #cite_link(<newstead2022>,
"(2022, appx. A)").

```agda
endpointPathPairsUnique : {i : Level} {A : Type i} {a : A}
                          (u : Σ A (λ x → a ＝ x)) →
                          pair a reflexive ＝ u
endpointPathPairsUnique (pair x reflexive) = reflexive
```

= Inverse operation on paths distributes over concatenation operation <note:a7028346-345c-49bc-99fe-2bf152286aa5>

#lemma(supplement: cite_link(<rijke2025>, "Rijke 2025, exer. 5.1"))[
    For all #link("note://261490cb-2887-4247-9a83-7f674e3c9651")[paths] $p
    ofType x = y$ and $q ofType y = z$, there is path
    $
        (p dot.op q)^(-1) = q^(-1) p^(-1).
    $
]
#proof[
    By #link("note://261490cb-2887-4247-9a83-7f674e3c9651")[path induction] on
    $p$, it suffices to construct a path
    $
        (refl_(x) dot.op q)^(-1) = q^(-1) dot.op refl_(x).
    $
    Since $refl_(x) dot.op q dot(eq) q$
    #link("note://984d4510-34b9-492f-a792-95a19117193e")[by definition], we can
    take the #link("note://95e3c813-ae44-4341-ac56-286cda078568")[inverse] of
    the #link("note://50f1bf11-5d39-455c-a39e-0d560ac5cee5")[right unit law for
    paths] to complete the construction.
]

See #link("note://95e3c813-ae44-4341-ac56-286cda078568")[Inverse operation on
paths] and #link("note://984d4510-34b9-492f-a792-95a19117193e")[Concatenation
operation on paths].

This pattern where the elements reverse when taking an inverse of a composition
shows up in group theory. For example, the inverse $(A B)^(-1)$ of the product
of two invertible matrices is $B^(-1) A^(-1)$.

```agda
⁻¹-distributesOver-∙ : {i : Level} {A : Type i} {x y z : A}
                       (p : x ＝ y) (q : y ＝ z) →
                       (p ∙ q)⁻¹ ＝ q ⁻¹ ∙ p ⁻¹
⁻¹-distributesOver-∙ reflexive q = ∙-unitʳ (q ⁻¹) ⁻¹
```

= Inverse concatenate and concatenate inverse on paths <note:ce7da014-650b-4bad-a1ed-ef56774b1f25>

#lemma(supplement: cite_link(<rijke2025>, "Rijke 2025, exer. 5.2"))[
    For #link("note://261490cb-2887-4247-9a83-7f674e3c9651")[paths] $p ofType x
    = y$, $q ofType y = z$, and $r ofType x = z$, if $p dot.op q = r$ then
    $
        q = p^(-1) dot.op r quad "and" quad p = r dot.op q^(-1).
    $
]
#proof[
    First, apply #link("note://261490cb-2887-4247-9a83-7f674e3c9651")[path
    induction] to $p$. Then our goal becomes
    $
        refl_(x) dot.op q = r -> q = (refl_(x))^(-1) dot.op r.
    $
    Since $refl_(x) dot.op q dot(eq) q$ and $(refl_(x))^(-1) dot.op r
    dot(eq) r$ by definition of the
    #link("note://984d4510-34b9-492f-a792-95a19117193e")[concatenation] and
    #link("note://95e3c813-ae44-4341-ac56-286cda078568")[inverse] operations,
    this reduces to the implication
    $
        q = r -> q = r,
    $
    so we can take the
    #link("note://efea6413-096d-4249-8ef0-a4de74fcee13")[identity map].

    Next, apply path induction to $q$. Now our goal is
    $
        p dot.op refl_(y) = r -> p = r dot.op (refl_(y))^(-1).
    $
    Let $alpha ofType p dot.op refl_(y) = r$. Then
    $
        p & = p dot.op refl_(y) && "by the inverse of the right unit law" \
            & = r && "using " med alpha \
            & = r dot.op refl_(y) && "by the inverse of the right unit law" \
            & = r dot.op (refl_(y))^(-1) && "by definition."
    $
    (See the #link("note://50f1bf11-5d39-455c-a39e-0d560ac5cee5")[unit laws for
    path concatenation].) This completes the construction.
]

See #link("note://95e3c813-ae44-4341-ac56-286cda078568")[inverse] and
#link("note://984d4510-34b9-492f-a792-95a19117193e")[concatenation] operations
on paths.

```agda
⁻¹∙ : {i : Level} {A : Type i} {x y z : A}
      {p : x ＝ y} {q : y ＝ z} {r : x ＝ z} →
      p ∙ q ＝ r → q ＝ p ⁻¹ ∙ r
⁻¹∙ {p = reflexive} {q = q} {r = r} = identity

∙⁻¹ : {i : Level} {A : Type i} {x y z : A}
      {p : x ＝ y} {q : y ＝ z} {r : x ＝ z} →
      p ∙ q ＝ r → p ＝ r ∙ q ⁻¹
∙⁻¹ {p = p} {q = reflexive} {r = r} α =
  p
    ＝[ ∙-unitʳ p ⁻¹ ]
  p ∙ reflexive
    ＝[ α ]
  r
    ＝[ ∙-unitʳ r ⁻¹ ]
  r ∙ reflexive ∎
```

= Inverse operation on paths is its own inverse <note:502e4b53-5266-4e05-9a62-48caa2a3d3e1>

The #link("note://95e3c813-ae44-4341-ac56-286cda078568")[inverse operation] on
#link("note://261490cb-2887-4247-9a83-7f674e3c9651")[paths] is its own
#link("note://32c2ca55-63ba-411b-9052-676a51fd16a1")[inverse].

#lemma(
    label: "51",
    supplement: cite_link(<rijke2025>, "Rijke 2025, exer. 9.1")
)[
    Let $A$ be any type. For every $x, y ofType A$, the the
    #link("note://95e3c813-ae44-4341-ac56-286cda078568")[inverse operations]
    $-^(-1) ofType x = y -> y = x$ and $-^(-1) ofType y = x -> x = y$ are
    #link("note://32c2ca55-63ba-411b-9052-676a51fd16a1")[inverses].
]
#proof[
    The #link("note://32c2ca55-63ba-411b-9052-676a51fd16a1")[required
    homotopies] hold #link("note://95e3c813-ae44-4341-ac56-286cda078568")[by
    definition of the inverse operation on paths].
]

```agda
⁻¹⁻¹-inverse :
  {i : Level} {A : Type i} {x y : A} →
  Inverse (_⁻¹ {x = x} {y = y}) (_⁻¹ {x = y} {y = x})
⁻¹⁻¹-inverse {x = x} {y = y} = pair H K
  where
  H : _⁻¹ ∘ _⁻¹ ∼ (identity {_} {x ＝ y})
  H reflexive = reflexive

  K : _⁻¹ ∘ _⁻¹ ∼ (identity {_} {y ＝ x})
  K reflexive = reflexive

⁻¹-isEquivalence :
  {i : Level} {A : Type i} {x y : A} →
  IsEquivalence (_⁻¹ {x = x} {y = y})
⁻¹-isEquivalence {x = x} {y = y} = inverse→isEquivalence _⁻¹ _⁻¹ ⁻¹⁻¹-inverse
```

= Path concatenation inverses <note:a0b593a9-3e6c-47b8-8160-d8ab79c4dd9b>

#link("note://32c2ca55-63ba-411b-9052-676a51fd16a1")[Inverses] for the
#link("note://984d4510-34b9-492f-a792-95a19117193e")[concatenation operation on
paths] in both arguments (also see
#link("note://95e3c813-ae44-4341-ac56-286cda078568")[Inverse operation on
paths]).
 
#lemma(
    label: "13",
    supplement: cite_link(<rijke2025>, "Rijke 2025, exer. 9.1.")
)[
    Fix a #link("note://261490cb-2887-4247-9a83-7f674e3c9651")[path] $p ofType x
    = y$. The functions
    $
        concat(p) & ofType y = z → x = z, \
        concat(p^(-1)) & ofType x = z → y = z
    $
    are #link("note://32c2ca55-63ba-411b-9052-676a51fd16a1")[inverses].

]
#proof[
    We #link("note://32c2ca55-63ba-411b-9052-676a51fd16a1")[need] to construct
    #link("note://3cb1b8ca-2a77-4c8a-b726-ed8f10dfd208")[homotopies]
    $
        H ofType concat(p^(-1)) dot.op concat(p) ~ & id_(y = z), \
        K ofType concat(p) dot.op concat(p^(-1)) ~ & id_(x = z).
    $
    For $H$, fix $q ofType y = z$. Then take the path given by
    $
        p^(-1) dot.op (p dot.op q)
            & = (p^(-1) dot.op p) dot.op q && "by associativity" \
            & = refl_(y) dot.op q && "by the left inverse law" \
            & = q && "by the left unit law"
    $
    (see #link("note://f2110298-afe0-4b63-9ef8-923f003cd631")[Concatenation on
    paths is associative],
    #link("note://ac149ae0-bd8c-4206-a7bf-eb6e7fa1575e")[Inverse operation on
    paths satisfies inverse laws], and
    #link("note://50f1bf11-5d39-455c-a39e-0d560ac5cee5")[Concatenation on paths
    satisfies the left and right unit laws with respect to reflexivity]).

    Similarly, for $K$, fix $r ofType x = z$ and take the path given by
    $
        p dot.op (p^(-1) dot.op r) = (p dot.op p^(-1)) dot.op r
        = refl_(x) dot.op r = r.
    $
]

```agda
∙-inverse : {i : Level} {A : Type i} {x y z : A}
            (p : x ＝ y) →
            Inverse (_∙_ {z = z} p) (_∙_ (p ⁻¹))
∙-inverse {_} {A} {x} {y} {z} p = pair H K
  where
  H : (_∙_ (p ⁻¹)) ∘ (_∙_ p) ∼ (identity {_} {y ＝ z})
  H q = (p ⁻¹ ∙ (p ∙ q))
          ＝[ ∙-associative (p ⁻¹) p q ⁻¹ ]
        (p ⁻¹ ∙ p) ∙ q
          ＝[ pathAction (flip _∙_ q) (⁻¹-inverseˡ p) ]
        reflexive ∙ q
          ＝[ ∙-unitˡ q ]
        q ∎

  K : (_∙_ p) ∘ (_∙_ (p ⁻¹)) ∼ (identity {_} {x ＝ z})
  K r = (p ∙ (p ⁻¹ ∙ r))
          ＝[ ∙-associative p (p ⁻¹) r ⁻¹ ]
        (p ∙ p ⁻¹) ∙ r
          ＝[ pathAction (flip _∙_ r) (⁻¹-inverseʳ p) ]
        reflexive ∙ r
          ＝[ ∙-unitˡ r ]
        r ∎
```

#lemma(supplement: cite_link(<rijke2025>, "Rijke 2025, exer. 9.1"))[
    Fix a #link("note://261490cb-2887-4247-9a83-7f674e3c9651")[path] $q ofType y
    = z$. The functions
    $
        concat(-, q) ofType & x = y -> x = z, \
        concat(-, q^(-1)) ofType & x = z -> x = y
    $
    are #link("note://32c2ca55-63ba-411b-9052-676a51fd16a1")[inverses].
]
#proof[
    Analogous to #link("note://a0b593a9-3e6c-47b8-8160-d8ab79c4dd9b")[Lemma 13].
]

```agda
∙-inverse' : {i : Level} {A : Type i} {x y z : A}
             (q : y ＝ z) →
             Inverse (flip (_∙_ {x = x}) q) (flip _∙_ (q ⁻¹))
∙-inverse' {_} {A} {x} {y} {z} q = pair H K
  where
  H : (flip _∙_ (q ⁻¹)) ∘ (flip _∙_ q) ∼ (identity {_} {x ＝ y})
  H p = (p ∙ q) ∙ q ⁻¹
          ＝[ ∙-associative p q (q ⁻¹) ]
        p ∙ (q ∙ q ⁻¹)
          ＝[ pathAction (_∙_ p) (⁻¹-inverseʳ q) ]
        p ∙ reflexive
          ＝[ ∙-unitʳ p ]
        p ∎

  K : (flip _∙_ q) ∘ (flip _∙_ (q ⁻¹)) ∼ (identity {_} {x ＝ z})
  K p = (p ∙ q ⁻¹) ∙ q
          ＝[ ∙-associative p (q ⁻¹) q ]
        p ∙ (q ⁻¹ ∙ q)
          ＝[ pathAction (_∙_ p) (⁻¹-inverseˡ q) ]
        p ∙ reflexive
          ＝[ ∙-unitʳ p ]
        p ∎
```

= Transport along a path is inverse to transport along the inverse path <note:985f36e7-d07e-4742-ac8c-b7c0dfe1def8>

#link("note://1229c654-047b-4517-9f4c-df4c03224d02")[Transporting] along a
#link("note://261490cb-2887-4247-9a83-7f674e3c9651")[path] and transporting
along the #link("note://95e3c813-ae44-4341-ac56-286cda078568")[inverse] of the
path are #link("note://32c2ca55-63ba-411b-9052-676a51fd16a1")[inverse
functions].
 
#lemma(
    label: "37",
    supplement: cite_link(<rijke2025>, "Rijke 2025, exer. 9.1")
)[
    Let $B$ be a #link("note://b05d0e2e-b6ab-45ab-9277-9559f4ee5e1f")[type
    family] over a type $A$ and let $p ofType x = y$ be a
    #link("note://261490cb-2887-4247-9a83-7f674e3c9651")[path] between elements
    $x, y ofType A$. Then the functions
    $
        tr_(B)(p) ofType & B(x) -> B(y), \
        tr_(B)(p^(-1)) ofType & B(y) -> B(x).
    $
    are #link("note://32c2ca55-63ba-411b-9052-676a51fd16a1")[inverses].
]
#proof[
    By #link("note://261490cb-2887-4247-9a83-7f674e3c9651")[path induction], it
    suffices to assume $p$ is $refl_(x)$. In this case, both
    #link("note://32c2ca55-63ba-411b-9052-676a51fd16a1")[required homotopies]
    hold #link("note://1229c654-047b-4517-9f4c-df4c03224d02")[by definition].
]

```agda
transportInverse : {i j : Level} {A : Type i} {B : A → Type j} {x y : A} →
                   (p : x ＝ y) →
                   Inverse (transport B p) (transport B (p ⁻¹))
transportInverse {_} {_} {A} {B} {x} {y} reflexive = pair H K
  where
  H : (transport B (reflexive ⁻¹)) ∘ (transport B reflexive) ∼
      (identity {_} {B x})
  H z = reflexive

  K : (transport B reflexive) ∘ (transport B (reflexive ⁻¹)) ∼
      (identity {_} {B y})
  K w = reflexive
```

= Family of identity types is reflexive <note:66b650cf-b748-49bd-8a08-edf38950bb2e>
 
#lemma[
    The #link("note://261490cb-2887-4247-9a83-7f674e3c9651")[family of identity
    types] is #link("note://7e7a1c6f-6051-4526-83e9-01d030717ea5")[reflexive].
]
#proof[
    Let $A$ be any type. For each $x ofType A$, take $refl_(x) ofType x = x$.
]

= Disequality is irreflexive <note:179cce1e-612e-4f8c-b176-a825693f9b87>

#lemma[
    #link("note://3cb5f252-202d-45a6-a77f-c7db57262632")[Disequality] is
    #link("note://088c9e40-5313-4e02-96df-58368e796ebe")[irreflexive].
]
#proof[
    Let $A$ be any type and let $x ofType A$. If we had $f ofType x != x$,
    we could apply $f$ to $refl_(x) ofType x = x$ and obtain a contradiction.
]

```agda
≠-irreflexive : {i : Level} {A : Type i} →
                Irreflexive {A = A} _≠_
≠-irreflexive x = absurd reflexive
```
 
= Disequality is symmetric <note:addb74f1-e36c-4c79-bbb7-3d2b251e5a88>

#lemma[
    #link("note://3cb5f252-202d-45a6-a77f-c7db57262632")[Disequality] is
    #link("note://ef9aa02f-8f36-46f5-ab3b-829123f2a139")[symmetric].
]
#proof[
    Let $x, y ofType A$ for any type $A$. Suppose $f ofType x != y$. Then if
    there was a #link("note://261490cb-2887-4247-9a83-7f674e3c9651")[path] $p
    ofType y = x$, we could
    #link("note://95e3c813-ae44-4341-ac56-286cda078568")[invert] it to get
    $p^(-1) ofType x = y$, and then obtain a contradiction by applying $f$.
]
 
```agda
≠-symmetric : {i : Level} {A : Type i} →
              Symmetric {A = A} _≠_
≠-symmetric p = p ∘ _⁻¹
```

= Type of endpoint-path pairs is contractible <note:0505440a-b3cf-41ad-b847-df4a87400d7a>
 
#theorem(
    label: "46",
    supplement: cite_link(<rijke2025>, "Rijke 2025, thm. 10.1.4")
)[
    Let $A$ be a type. For any $a ofType A$, the type of
    #link("note://536f383d-a59f-4ad3-8c15-82f0a7b9822d")[endpoint-path pairs]
    $
        sigmaType(x, A) a = x
    $
    is #link("note://f817901c-750e-4575-a259-d83730424ade")[contractible].
]
#proof[
    Take $(a, refl_(a)) ofType sigmaType(x, A) a = x$ as the
    #link("note://f817901c-750e-4575-a259-d83730424ade")[center of
    contraction]. The
    #link("note://f817901c-750e-4575-a259-d83730424ade")[contraction] is given
    by #link("note://536f383d-a59f-4ad3-8c15-82f0a7b9822d")[Lemma 1].
]

```agda
endpointPathContractible : {i : Level} {A : Type i}
                           (a : A) → IsContractible (Σ A (λ x → a ＝ x))
endpointPathContractible a =
  pair (pair a reflexive) endpointPathPairsUnique
```
