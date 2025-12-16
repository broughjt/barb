#import("../../../../../library/template.typ"): *

#show: template

```agda
module Base.Decision.Properties where

open import Base.Decision.Core
open import Base.Decision.Definitions
open import Base.Function.Core
open import Base.Function.Definitions
open import Base.Function.Negation
open import Base.Universe
open import Data.Coproduct.Core
open import Data.Coproduct.Definitions as Coproduct
open import Data.Sigma.Core
open import Data.Sigma.Definitions
```

= Logically equivalent and decidable implies decidable <note:d70b37f9-d122-414e-98b2-19ac5af7a159>

#lemma(supplement: cite_link(<rijke2025>, "Rijke 2025, lem. 8.1.6"))[
    If types $A$ and $B$ are
    #link("note://27061ddb-2091-46c1-8752-21db2ab57f44")[logically equivalent],
    then there is a
    #link("note://36f1a370-ca8c-4053-8ee6-d284b50b90e5")[decision] for $A$ if
    and only if $B$ there is a decision $B$.

    Symbolically, if $A arrow.l.r B$ then $Decision(A) arrow.l.r
    Decision(B)$.

    If $A$ and $B$ are propositions, we
    #link("note://36f1a370-ca8c-4053-8ee6-d284b50b90e5")[can phrase this] by
    saying that if $A$ and $B$ are logically equivalent then $A$ is
    #link("note://36f1a370-ca8c-4053-8ee6-d284b50b90e5")[decidable] if and only
    if $B$ is decidable.
]
#proof[
    We have $f ofType A -> B$ and $g ofType B -> A$ by assumption.

    It suffices to show the direction $Decision(A) -> Decision(B)$, since the
    other direction is then obtained by swapping the types $A$ and $B$. We
    proceed by cases on $A + not A$.

    1. If $x ofType A$, apply $f ofType A -> B$ to obtain $f(x) ofType B$.
    2. Otherwise we have $h ofType not A$. We can take the
       #link("note://1da6e034-c251-45d1-a83f-513aa5eefeeb")[contrapositive] of $g
       ofType B -> A$, which, when applied to $h ofType not A$, gives $not B$.
]

```agda
↔-decide→decide : {i j : Level} {A : Type i} {B : Type j} →
                  (A ↔ B) → Decision A → Decision B
↔-decide→decide (pair f g) = Coproduct.map f (contrapositive g)

↔→decide↔decide : {i j : Level} {A : Type i} {B : Type j} →
                  (A ↔ B) → (Decision A ↔ Decision B)
↔→decide↔decide p = pair (↔-decide→decide p) (↔-decide→decide $ swap p)
```

= Decision for decision type implies decision <note:24d59546-08a1-430c-9e27-60a29f26ab06>
 
#lemma(supplement: cite_link(<rijke2025>, "Rijke 2025, exer. 8.2"))[
    Let $A$ be a type. If there is a
    #link("note://36f1a370-ca8c-4053-8ee6-d284b50b90e5")[decision] for the type
    $Decision(A)$ then there is a decision for $A$. In other words, there is a
    map
    $
        Decision(Decision(A)) -> Decision(A).
    $
]
#proof[
    If $inject1(d) ofType Decision(Decision(A))$ then we obtain a decision $d
    ofType Decision(A)$. Otherwise, we have $inject2(f) ofType
    Decision(Decision(A))$, where $f ofType not Decision(A)$. Then to construct
    a map $A -> emptyType$, we can take the
    #link("note://bc9568f6-830b-4b4e-9aab-1808b1127cb0")[composition]
    $
        A & ->^(inject_(2)) Decision(A) & ->^f emptyType.
    $
]

```agda
decideDecide→decide : {i : Level} {A : Type i} →
                      Decision (Decision A) → Decision A
decideDecide→decide (inject₁ d) = d
decideDecide→decide (inject₂ f) = inject₂ $ f ∘ inject₁
```
