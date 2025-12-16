#import("../../../../../library/template.typ"): *

#show: template

```agda
module Base.Function.Definitions where

open import Base.Identity.Core
open import Base.Identity.Definitions renaming (_⁻¹ to _⁻¹'; _∙_ to _∙'_)
open import Base.Universe
open import Data.Sigma.Core
```

= Logical biconditional <note:27061ddb-2091-46c1-8752-21db2ab57f44>

Under the Curry-Howard interpretation, logical implication $P ==> Q$ is
expressed as a function type $P -> Q$, where $P$ and $Q$ are types. Therefore,
we express the notion of the *logical biconditional*, or *biimplication*, or
*logical equivalence* between two types $A$ and $B$ as the
#link("note://23a01b78-e433-4a66-8915-bfda82ee149a")[product] $(A -> B) times (B
-> A)$ @rijke2025[exer. 4.3].

```agda
_↔_ : {i j : Level} (A : Type i) (B : Type j) → Type (i ⊔ j)
A ↔ B = (A → B) × (B → A)
```

= (Type-theoretic) Homotopy <note:3cb1b8ca-2a77-4c8a-b726-ed8f10dfd208>
 
Let $f, g ofType piType(x, A) B(x)$ be dependent functions. The type of
*homotopies* from $f$ to $g$, written $f ~ g$ is the type of pointwise
#link("note://261490cb-2887-4247-9a83-7f674e3c9651")[identifications] of $f$ and
$g$:
$
    f ~ g := piType(x, A) f(x) = g(x)
$

@rijke2025[def. 9.1.2].

```agda
_∼_ : {i j : Level} {A : Type i} {B : A → Type j} →
      ((x : A) → B x) → ((x : A) → B x) → Type (i ⊔ j)
_∼_ {A = A} f g = (x : A) → f x ＝ g x

infix 3 _∼_
```

= Reflexive homotopy <note:61b2c016-4fa5-4f6e-aab5-edc45a528681>

#lemma(supplement: cite_link(<rijke2025>, "Rijke 2025, def. 9.1.5"))[
    There is a canonical
    #link("note://3cb1b8ca-2a77-4c8a-b726-ed8f10dfd208")[homotopy] between any
    dependent function $f ofType piType(x, A) B(x)$ and itself $refl_(f) ofType
    f ~ f$, which we refer to as the *reflexive homotopy*.
]
#proof[
    For each $f ofType piType(x, A) B(x)$, let $refl_(f) := lambda x
    . refl_(f(x)) ofType f ~ f$.
]

= Inverse of a homotopy <note:926fa23f-6495-407a-a492-9aec9e451930>
 
#lemma(supplement: cite_link(<rijke2025>, "Rijke 2025, def. 9.1.5"))[
    There is an *inverse operation* on
    #link("note://3cb1b8ca-2a77-4c8a-b726-ed8f10dfd208")[homotopies], which
    sends homotopies $f ~ g$ to homotopies $g ~ f$. That is, there is an
    operation
    $
        piType(f, g, piType(x, A) B(x)) f ~ g -> g ~ f.
    $
]
#proof[
    If $H ofType f ~ g$ then $lambda x . (H x)^(-1) ofType g ~ f$ (see
    #link("note://95e3c813-ae44-4341-ac56-286cda078568")[Inverse operation on
    paths]).
]

```agda
_⁻¹ : {i j : Level} {A : Type i} {B : A → Type j} →
      {f g : (x : A) → B x} →
      f ∼ g → g ∼ f
H ⁻¹ = λ x → (H x) ⁻¹'
```

= Homotopy concatenation <note:a3eaa21d-b0a4-4aed-80fd-ed5aeb914aab>

#lemma(supplement: cite_link(<rijke2025>, "Rijke 2025, def. 9.1.5"))[
    There is a *concatenation operation* on
    #link("note://3cb1b8ca-2a77-4c8a-b726-ed8f10dfd208")[homotopies] which given
    homotopies $f ~ g$ and $g ~ h$ produces a homotopy $f ~ h$. In other words,
    there is a function
    $
        piType(f, g, h, piType(x, A) B(x)) f ~ g -> g ~ h -> f ~ h.
    $
]
#proof[
    Given $H ofType f ~ g$ and $K ofType g ~ h$, let $H dot.op K := lambda x
    . H(x) dot.op K(x)$ (see
    #link("note://984d4510-34b9-492f-a792-95a19117193e")[Concatenation operation
    on paths]).
]
