#import("../../../../../library/template.typ"): *

#show: template

```agda
module Foundation.Function.Negation where

open import Data.Empty as 𝟎
open import Foundation.Function.Definitions
open import Foundation.Universe
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
absurd x f = 𝟎.induction (f x)
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
