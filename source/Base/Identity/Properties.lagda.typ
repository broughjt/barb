#import("../../../../../library/template.typ"): *

#show: template

```agda
module Base.Identity.Properties where

open import Base.Function.Core
open import Base.Identity.Core
open import Base.Identity.Definitions
open import Base.Universe
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
