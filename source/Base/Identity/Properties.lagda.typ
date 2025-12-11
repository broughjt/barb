#import("../../../../../library/template.typ"): *

#show: template

```agda
module Base.Identity.Properties where

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
