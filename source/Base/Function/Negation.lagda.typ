#import("../../../../../library/template.typ"): *

#show: template

```agda
module Base.Function.Negation where

open import Base.Function.Core
open import Base.Universe.Core
open import Data.Coproduct.Core as Coproduct
open import Data.Empty as Empty
```

= Negation of a type <note:16ffba35-7712-4eb7-8902-0812e529aa16>
 
The *negation* of a type $A$, written $not A$, is defined as the function type
$A -> emptyType$ (see #link("note://9d7cf197-7f2a-4633-aa63-1c9df1429a13")[Empty
type]). If $A$ comes equipped with an element of the type $not A$, we say the
$A$ is *empty* @rijke2025[def. 4.3.2].

```agda
¬_ : {i : Level} → Type i → Type i
¬ A = A → 𝟎

infix 3 ¬_
```

= Proof of negation by absurdity <note:5e5e6ae4-329b-473f-b13c-c2cbd77534b6>

#lemma(supplement: cite_link(<rijke2025>, [Rijke 2025, Rem. 4.3.3]))[
    If both $A$ and $not A$ hold, then $B$ holds for any type $B$.
]
#proof[
    Suppose $x ofType A$ and $f ofType A -> emptyType$. Apply $f$ to $x$ to
    obtain $f(x) ofType emptyType$. Then apply recursion on the
    #link("note://9d7cf197-7f2a-4633-aa63-1c9df1429a13")[empty type] to obtain
    an element of $B$.
]

```agda
absurd : {i j : Level} {A : Type i} {B : Type j} →
         A → ¬ A → B
absurd x f = Empty.recursion (f x)
```

= Implications imply their contrapositives <note:b2b44f1f-5678-4125-a6e5-263a5fa645cf>

#lemma(supplement: cite_link(<rijke2025>, [Rijke 2025, Prop. 4.3.4]))[
    For any two types $P$ and $Q$, $P -> Q$ implies $not Q -> not P$.

    In other words, there is a function
    $
        (P -> Q) -> (not Q -> not P).
    $
]
#proof[
    If we have $f ofType P -> Q$ and $g ofType Q -> emptyType$ then their
    composition gives $g compose f ofType P -> emptyType$.
]

See #link("note://1da6e034-c251-45d1-a83f-513aa5eefeeb")[Contrapositive of an
impliciation].

```agda
contrapositive : {i j : Level} {A : Type i} {B : Type j} →
                 (A → B) → (¬ B → ¬ A)
contrapositive f g = g ∘ f
```

= Negation resolution <note:4af48c11-22e0-4aae-89eb-fad6d4320836>
 
#lemma(label: "5", supplement: cite_link(<rijke2025>, [Rijke 2025, Prop 4.4.3]))[
    Let $A$ and $B$ be types. If $B$ is empty, then $A + B$ implies
    $A$. Similarly, if $A$ is empty, then $A + B$ implies $B$. In other words,
    there are functions
    $
        not B & -> (A + B -> A), \
        not A & -> (A + B -> B).
    $
]
#proof[
    We prove the first implication $not B -> (A + B -> A)$; the second is
    analogous.

    Let $g ofType not B$. By the
    #link("note://001d31c7-7fb6-4878-883a-ff464bb9c0a8")[induction principle for
    coproducts], it suffices to construct functions
    $
        A -> A quad "and" quad B -> A.
    $
    Take the #link("note://efea6413-096d-4249-8ef0-a4de74fcee13")[identity
    function] $id_(A)$ for $A -> A$. For $B -> A$,
    #link("note://bc9568f6-830b-4b4e-9aab-1808b1127cb0")[compose] $g$ with the
    recursor for the #link("note://9d7cf197-7f2a-4633-aa63-1c9df1429a13")[empty
    type] $recursion_(emptyType) ofType emptyType -> A$ to obtain
    $recursion_(emptyType) compose g : B -> A$ as needed.
]

See #link("note://001d31c7-7fb6-4878-883a-ff464bb9c0a8")[Coproduct type].

```agda
resolve₁ : {i j : Level} {A : Type i} {B : Type j} →
           ¬ B → (A ＋ B → A)
resolve₁ g = Coproduct.recursion identity (Empty.recursion ∘ g)

resolve₂ : {i j : Level} {A : Type i} {B : Type j} →
           ¬ A → (A ＋ B → B)
resolve₂ f = Coproduct.recursion (Empty.recursion ∘ f) identity
```
