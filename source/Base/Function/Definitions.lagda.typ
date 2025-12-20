#import("../../../../../library/template.typ"): *

#show: template

```agda
module Base.Function.Definitions where

open import Base.Function.Core
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

```agda
reflexiveHomotopy : {i j : Level} {A : Type i} {B : A → Type j} →
                    ((f : (x : A) → B x) → f ∼ f)
reflexiveHomotopy f x = reflexive
```

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

infixr 8 _⁻¹
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

```agda
_∙_ : {i j : Level} {A : Type i} {B : A → Type j}
      {f g h : (x : A) → B x} →
      f ∼ g → g ∼ h → f ∼ h
H ∙ K = λ x → (H x) ∙' (K x)

infixl 7 _∙_
```

= Whiskering operations on homotopies <note:7805061a-565d-4412-9ca4-acb998e89555>
 
#cite(<rijke2025>, form: "prose") defines the *whiskering* operations on
homotopies as a notion of composition between functions and homotopies
(def. 9.1.7). Suppose we have $H ofType f ~ g$ between functions $f,
g ofType A -> B$, and let $h ofType B -> C$ be another function. We define
$
    h dot.op H := lambda x . ap_(h)(H(x)) ofType h compose f ~ h compose g.
$
Similarly, let $f ofType A -> B$ and suppose we have $H ofType g ~ h$ between
two functions $g, h ofType B -> C$. We define
$
    H dot.op f := lambda x . H(f(x)) ofType g compose f ~ h compose f.
$

```agda
_∙ₗ_ : {i j k : Level} {A : Type i} {B : Type j} {C : Type k}
       {f g : A → B}
       (h : B → C) (H : f ∼ g) → h ∘ f ∼ h ∘ g
h ∙ₗ H = (pathAction h) ∘ H

_∙ᵣ_ : {i j k : Level} {A : Type i} {B : Type j} {C : Type k}
       {g h : B → C} →
       (H : g ∼ h) (f : A → B) → g ∘ f ∼ h ∘ f
H ∙ᵣ f = H ∘ f

infixl 7 _∙ₗ_
infixl 7 _∙ᵣ_
```

= Sections, retractions, inverses, and equivalences <note:32c2ca55-63ba-411b-9052-676a51fd16a1>
 
For each of the following definitions, we follow #cite(<rijke2025>, form:
"prose", supplement: "def. 1.1.7").

A *section* of a map $f ofType A -> B$ is a map $g ofType B -> A$ equipped with
a #link("note://3cb1b8ca-2a77-4c8a-b726-ed8f10dfd208")[homotopy] $f compose g ~
id_(B)$ witnessing that $g$ is a right inverse of $f$.

```agda
RightInverse : {i j : Level} {A : Type i} {B : Type j} →
               (A → B) → (B → A) → Type j
RightInverse {B = B} f g = f ∘ g ∼ (identity {_} {B})

Section : {i j : Level} {A : Type i} {B : Type j} →
          (A → B) → Type (i ⊔ j)
Section {A = A} {B = B} f = Σ (B → A) (RightInverse f)
```

A *retraction* of $f ofType A -> B$ is a map $g ofType B -> A$ equipped with a
homotopy $g compose f ~ id_(A)$ witnessing that $g$ is a left inverse of $f$.

```agda
LeftInverse : {i j : Level} {A : Type i} {B : Type j} →
              (A → B) → (B → A) → Type i
LeftInverse {A = A} f g = g ∘ f ∼ (identity {_} {A})

Retraction : {i j : Level} {A : Type i} {B : Type j} →
             (A → B) → Type (i ⊔ j)
Retraction {A = A} {B = B} f = Σ (B → A) (LeftInverse f)
```

A function $g ofType B -> A$ is an *inverse* of a function $f ofType A -> B$ if
$g$ is both a section and a retraction of $f$, that is, if it is both a left and
right invese inverse of $f$.

```agda
Inverse : {i j : Level} {A : Type i} {B : Type j} →
          (A → B) → (B → A) → Type (i ⊔ j)
Inverse f g = LeftInverse f g × RightInverse f g

HasInverse : {i j : Level} {A : Type i} {B : Type j} →
             (A → B) → Type (i ⊔ j)
HasInverse {A = A} {B = B} f = Σ (B → A) (Inverse f)
```

A function $f ofType A -> B$ is an *equivalence* if it has both a section and a retraction.

```agda
IsEquivalence : {i j : Level} {A : Type i} {B : Type j} →
                (A → B) → Type (i ⊔ j)
IsEquivalence f = Section f × Retraction f
```

We write $A tilde.eq B$ for the type of all equivalences from a type $A$ to a
type $B$.

```agda
_≃_ : {i j : Level} → Type i → Type j → Type (i ⊔ j)
A ≃ B = Σ (A → B) IsEquivalence

infix 3 _≃_
```

= Involutive <note:47767cc9-0064-45d3-8735-203b3236976d>
 
A function $f ofType A -> A$ from a type to itself is *involutive* if it serves
as its own #link("note://32c2ca55-63ba-411b-9052-676a51fd16a1")[inverse].

```agda
Involutive : {i : Level} {A : Type i} →
             (A → A) → Type i
Involutive f = Inverse f f
```
