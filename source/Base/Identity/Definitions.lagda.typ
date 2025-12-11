#import("../../../../../library/template.typ"): *

#show: template

```agda
module Base.Identity.Definitions where

open import Base.Function.Negation
open import Base.Identity.Core
open import Base.Universe
```

= Disequality <note:3cb5f252-202d-45a6-a77f-c7db57262632>

Given a type $A$ and elements $x, y ofType A$, we define *disequality* between
$x$ and $y$, written $x != y$, as the
#link("note://16ffba35-7712-4eb7-8902-0812e529aa16")[negation] of the
#link("note://261490cb-2887-4247-9a83-7f674e3c9651")[identity type] $x = y$
@univalentfoundationsprogram2013[sec. 1.12.3].

```agda
_≠_ : {i : Level} {A : Type i} → A → A → Type i
x ≠ y = ¬ x ＝ y

infix 4 _≠_
```

When $x != y$ holds, we say $x$ and $y$ are *unequal* or *not equal*. We refer
to $!=$ as "disequality" because the term "inequality" is traditionally reserved
for relations which constitute a strict or non-strict partial order.

= Concatenation operation on paths <note:984d4510-34b9-492f-a792-95a19117193e>

#lemma(
    supplement:
    [Path concatenation; #cite_link(<rijke2025>, "Rijke 2025, def. 5.2.1")])[
        Let $A$ be a type. For every $x, y, z ofType A$, there is a
        *concatenation operation*
        $
            sans("concat") ofType (x = y) -> (y = z) -> (x = z).
        $

        Often, we will write $p dot.op q$ for $sans("concat")(p, q)$.
]
#proof[
    Let $x, y, z ofType A$, $p ofType x = y$, and $q ofType y = z$. By
    #link("note://261490cb-2887-4247-9a83-7f674e3c9651")[path induction] on $p$,
    it suffices to prove the statement when $y$ is $x$ and $p$ is
    $refl_(x)$. But then $q$ has type $x = z$. Since our goal is to produce an
    element of $x = z$, we can take $q ofType x = z$, finishing the
    construction.
]

```agda
_∙_ : {i : Level} {A : Type i} {x y z : A} → x ＝ y → y ＝ z → x ＝ z
reflexive ∙ q = q

infixl 7 _∙_
```

= Inverse operation on paths <note:95e3c813-ae44-4341-ac56-286cda078568>
 
#lemma(supplement: [Path inverses; #cite_link(<rijke2025>, "Rijke 2025, def. 5.2.2")])[
    For every type $A$ and every $x, y ofType A$, there is an *inverse
    operation*
    $
        sans("concat") ofType (x = y) -> (y = x).
    $

    Given a path $p ofType x = y$, we usually write $p^(-1) ofType y = x$ in
    place of $sans("inverse")(p) ofType y = x$.
]
#proof[
    Let $x ofType A$ and apply
    #link("note://261490cb-2887-4247-9a83-7f674e3c9651")[path induction]. Then
    it remains to construct an element of type $x = x$, so we can take $refl_(x)
    ofType x = x$.
]

```agda
_⁻¹ : {i : Level} {A : Type i} {x y : A} → x ＝ y → y ＝ x
reflexive ⁻¹ = reflexive
```
