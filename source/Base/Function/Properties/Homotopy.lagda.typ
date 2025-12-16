#import("../../../../../../library/template.typ"): *

#show: template

```agda
module Base.Function.Properties.Homotopy where

open import Base.Universe
open import Base.Identity.Core
open import Base.Identity.Definitions renaming (_⁻¹ to _⁻¹'; _∙_ to _∙'_)
import Base.Identity.Properties as Identity
open import Base.Function.Definitions
```

= Concatenation on homotopies is associative up to homotopy <note:2bb9c32b-d3eb-4693-a814-c37b23aac880>
 
#lemma(supplement: cite_link(<rijke2025>, "Rijke 2025, prop. 9.1.6"))[
    #link("note://a3eaa21d-b0a4-4aed-80fd-ed5aeb914aab")[Concatenation] of
    #link("note://3cb1b8ca-2a77-4c8a-b726-ed8f10dfd208")[homotopies] is
    #link("note://9affcc46-5cf0-4627-b909-80ec3cba8a2d")[associative] up to
    homotopy, that is, for all homotopies $H ofType f ~ g$, $K ofType g ~ h$,
    and $L ofType h ~ i$, there is a homotopy
    $
        (H dot.op K) dot.op L ~ H dot.op (K dot.op L),
    $
    where $f, g, h, i ofType piType(x, A) B(x)$.
]
#proof[
    Fix $x ofType A$. We need to construct a
    #link("note://261490cb-2887-4247-9a83-7f674e3c9651")[path]
    $
        ((H dot.op K) dot.op L)(x) = (H dot.op (K dot.op L))(x).
    $
    This #link("note://a3eaa21d-b0a4-4aed-80fd-ed5aeb914aab")[evaluates to]
    $
        (H(x) dot.op K(x)) dot.op L(x) = H(x) dot.op (K(x) dot.op L(x)),
    $
    (where $H(x) ofType f(x) = g(x)$, $K(x) ofType g(x) = h(x)$, and $L(x)
    ofType h(x) = i(x)$).  Therefore we can obtain the needed path from the
    #link("note://f2110298-afe0-4b63-9ef8-923f003cd631")[associativity of path
    concatenation].
]

```agda
homotopyAssociative : {i j : Level} {A : Type i} {B : A → Type j}
                      {f g h i : (x : A) → B x} →
                      (H : f ∼ g) (K : g ∼ h) (L : h ∼ i) →
                      (H ∙ K) ∙ L ∼ H ∙ (K ∙ L)
homotopyAssociative H K L x = Identity.∙-associative (H x) (K x) (L x)
```

= Homotopy concatenation satisfies unit laws up to homotopy with respect to the reflexive homotopy <note:061ca7df-33a7-40f0-95ba-bb4f36a69e98>
 
#lemma(supplement: cite_link(<rijke2025>, "Rijke 2025, prop. 9.1.6"))[
    #link("note://a3eaa21d-b0a4-4aed-80fd-ed5aeb914aab")[Concatenation] of
    #link("note://3cb1b8ca-2a77-4c8a-b726-ed8f10dfd208")[homotopies] satisfies
    the left and right unit laws up to homotopy, with respect to the
    #link("note://61b2c016-4fa5-4f6e-aab5-edc45a528681")[reflexive
    homotopy]. In other words, for each homotopy $H ofType f ~ g$, there are
    homotopies
    $
        refl_(f) dot.op H ~ & H, \
        H dot.op refl_(g) ~ & H.
    $
]
#proof[
    Let $x ofType A$. This amounts to constructing
    #link("note://261490cb-2887-4247-9a83-7f674e3c9651")[paths]
    $
        refl_(f(x)) dot.op H(x) = & H(x), \
        H(x) dot.op refl_(g(x)) = & H(x)
    $
    for each $x ofType A$, which we obtain by applying the
    #link("note://50f1bf11-5d39-455c-a39e-0d560ac5cee5")[left and right unit
    laws] for paths.
]

```agda
∙-unitˡ : {i j : Level} {A : Type i} {B : A → Type j}
          {f g : (x : A) → B x}
          (H : f ∼ g) →
          (reflexiveHomotopy f) ∙ H ∼ H
∙-unitˡ H x = Identity.∙-unitˡ (H x)

∙-unitʳ : {i j : Level} {A : Type i} {B : A → Type j}
          {f g : (x : A) → B x} →
          (H : f ∼ g) →
          H ∙ (reflexiveHomotopy g) ∼ H
∙-unitʳ H x = Identity.∙-unitʳ (H x)
```

= Inverse operation on homotopies satisfies inverse laws up to homotopy <note:f9310375-020b-41c2-bc79-5fd5b2fa7f24>
 
#lemma(supplement: cite_link(<rijke2025>, "Rijke 2025, prop 9.1.6"))[
    The #link("note://926fa23f-6495-407a-a492-9aec9e451930")[inverse operation]
    on #link("note://3cb1b8ca-2a77-4c8a-b726-ed8f10dfd208")[homotopies]
    satisfies the inverse laws up to homotopy with respect to the
    #link("note://61b2c016-4fa5-4f6e-aab5-edc45a528681")[reflexive
    homotopy]. That is, for each homotopy $H ofType f ~ g$, there are homotopies
    $
        H^(-1) dot.op H ~ & refl_(g), \
        H dot.op H^(-1) ~ & refl_(f).
    $
]
#proof[
    Fix $x ofType A$. We need to construct
    #link("note://261490cb-2887-4247-9a83-7f674e3c9651")[paths]
    $
        H^(-1)(x) dot.op H(x) = & refl_(g(x)), \
        H(x) dot.op H^(-1)(x) = & refl_(f(x)),
    $
    which we can obtain by applying the
    #link("note://ac149ae0-bd8c-4206-a7bf-eb6e7fa1575e")[inverse laws for paths]
    to the path $H(x)$.
]

```agda
⁻¹-inverseˡ : {i j : Level} {A : Type i} {B : A → Type j}
              {f g : (x : A) → B x} →
              (H : f ∼ g) →
              (H ⁻¹) ∙ H ∼ (reflexiveHomotopy g)
⁻¹-inverseˡ H x = Identity.⁻¹-inverseˡ (H x)

⁻¹-inverseʳ : {i j : Level} {A : Type i} {B : A → Type j}
              {f g : (x : A) → B x} →
              (H : f ∼ g) →
              H ∙ (H ⁻¹) ∼ (reflexiveHomotopy f)
⁻¹-inverseʳ H x = Identity.⁻¹-inverseʳ (H x)
```
