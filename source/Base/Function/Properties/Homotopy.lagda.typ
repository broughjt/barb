#import("../../../../../../library/template.typ"): *

#show: template

```agda
module Base.Function.Properties.Homotopy where

import Base.Identity.Properties as Identity
open import Base.Function.Core
open import Base.Function.Definitions
open import Base.Identity.Core
open import Base.Identity.Definitions renaming (_⁻¹ to _⁻¹'; _∙_ to _∙'_)
open import Base.Identity.Syntax
open import Base.Universe.Core
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

= Homotopy naturality <note:518711cc-ffe5-4ed7-b5e6-daa80d359c32>

#let app = math.sans("ap")
 
#lemma(supplement: cite_link(<rijke2025>, "Rijke 2025, def. 10.4.3"))[
    Let $f, g ofType A -> B$ be maps. Given a
    #link("note://3cb1b8ca-2a77-4c8a-b726-ed8f10dfd208")[homotopy] $H ofType f ~
    g$ and a #link("note://261490cb-2887-4247-9a83-7f674e3c9651")[path] $p
    ofType x = y$, there is a path
    $
        ap_(f)(p) dot.op H(y) = H(x) dot.op ap_(g)(p)
    $
    witnessing that the square

    #figure(
        diagram($
            f(x) fletchereq("d", app_(f)(p)) fletchereq("r", H(x)) & g(x) fletchereq("d", app_(g)(p), label-side: #left) \
            f(y) fletchereq("r", H(y), label-side: #right) & g(x)

        $)
    )
    commutes.
]

According to #cite(<rijke2025>, form: "prose", supplement: "def. 10.4.3"), this
square is referred to as the *naturality square* of the homotopy $H$ at $p$.

#proof[
    By #link("note://261490cb-2887-4247-9a83-7f674e3c9651")[path induction] on
    $p$, it is sufficient to construct a path
    $
        ap_(f)(refl_(x)) dot.op H(x) = H(x) dot.op ap_(g)(refl_(x)).
    $
    By definition of the
    #link("note://7caf7ee0-9e2a-4761-bee9-25cd52820039")[action on paths], this
    evaluates to
    $
        refl_(f(x)) dot.op H(x) = H(x) dot.op refl_(g(x)),
    $
    which holds by the #link("note://50f1bf11-5d39-455c-a39e-0d560ac5cee5")[unit
    laws for paths].
]

```agda
homotopyNatural :
  {i j : Level} {A : Type i} {B : Type j}
  {x y : A} {f g : A → B} →
  (H : f ∼ g) (p : x ＝ y) →
  (pathAction f p) ∙' (H y) ＝ (H x) ∙' (pathAction g p)
homotopyNatural {x = x} H reflexive = Identity.∙-unitʳ (H x) ⁻¹'
```

= Homotopy naturality for the identity function <note:42940391-aee2-4aa4-8240-5a38a3c3ee37>

#lemma(supplement: cite_link(<rijke2025>, "Rijke 2025, def. 10.4.4"))[
    Let $f : A -> A$ be a map equipped with a
    #link("note://3cb1b8ca-2a77-4c8a-b726-ed8f10dfd208")[homotopy] $H ofType f ~
    id_(A)$. Then for all $x ofType A$, there is a
    #link("note://261490cb-2887-4247-9a83-7f674e3c9651")[path]
    $
        H(f(x)) = ap_(f)(H(x)).
    $

]

I'm leaving the paper proof unwritten because I don't really understand what's
going on here right now.

```agda
homotopyNaturalIdentity :
  {i : Level} {A : Type i}
  {f : A → A}
  (H : f ∼ identity)
  (x : A) →
  H (f x) ＝ pathAction f (H x)
homotopyNaturalIdentity {f = f} H x = r
  where
  p : pathAction f (H x) ∙' H x ＝ H (f x) ∙' pathAction identity (H x)
  p = homotopyNatural {x = f x} {y = x} {f = f} {g = identity} H (H x)

  q : H (f x) ∙' pathAction identity (H x) ＝ H (f x) ∙' (H x)
  q = pathAction (_∙'_ (H (f x))) (Identity.pathActionIdentity (H x)) ⁻¹'

  -- TODO: Replace this with a lemma that paths are cancellative
  r : H (f x) ＝ pathAction f (H x)
  r = H (f x)
        ＝[ Identity.∙-unitʳ (H (f x)) ⁻¹' ]
      H (f x) ∙' reflexive
        ＝[ pathAction (_∙'_ (H (f x))) (Identity.⁻¹-inverseʳ (H x) ⁻¹') ]
      H (f x) ∙' ((H x) ∙' (H x) ⁻¹')
        ＝[ Identity.∙-associative (H (f x)) (H x) (H x ⁻¹') ⁻¹' ]
      (H (f x) ∙' (H x)) ∙' (H x) ⁻¹'
        ＝[ pathAction (flip _∙'_ ((H x) ⁻¹')) ((p ∙' q) ⁻¹') ]
      (pathAction f (H x) ∙' H x) ∙' (H x) ⁻¹'
        ＝[ Identity.∙-associative (pathAction f (H x)) _ _ ]
      pathAction f (H x) ∙' (H x ∙' (H x) ⁻¹')
        ＝[ pathAction (_∙'_ $ pathAction f (H x))
                      (Identity.⁻¹-inverseʳ (H x)) ]
      pathAction f (H x) ∙' reflexive
        ＝[ (Identity.∙-unitʳ $ pathAction f (H x)) ]
      pathAction f (H x) ∎
```
