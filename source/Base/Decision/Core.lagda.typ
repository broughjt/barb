#import("../../../../../library/template.typ"): *

#show: template

```agda
module Base.Decision.Core where

open import Base.Function.Negation
open import Base.Universe
open import Data.Coproduct.Core
```

= Decision for a type <note:36f1a370-ca8c-4053-8ee6-d284b50b90e5>

A *decision* for a type $A$ is an element of the
#link("note://001d31c7-7fb6-4878-883a-ff464bb9c0a8")[coproduct] $A + not A$
(cf. #cite_link(<rijke2025>, "Rijke 2025, def. 8.1.1")).
A *decision procedure* for a
#link("note://b05d0e2e-b6ab-45ab-9277-9559f4ee5e1f")[type family] $P ofType A ->
cal(U)$ is a dependent function

$
    piType(x, A) P(x) + not P(x),
$
which assigns to each $x ofType A$ a decision for the
#link("note://85839d30-6530-4e54-a8ba-efd1c8709928")[fiber] $P(x)$.

If the type of decisions $A + not A$ for a type $A$ is inhabited, we say the
type $A$ is *decidable*. However, I find this terminology a bit misleading,
since "decidable" sounds like a predicate which applies to arbitrary types $A$,
but in general the type $A + not A$ need not be a proposition. I will use the
"decidable" language when it is clear that the types being dealt with are
propositions, but when this is not the case I will try to use the more explicit
"decision" language.

```agda
Decision : {i : Level} → Type i → Type i
Decision A = A ＋ ¬ A

DecisionProcedure : {i j : Level} {A : Type i} →
                    (A → Type j) → Type (i ⊔ j)
DecisionProcedure {A = A} B = (x : A) → Decision (B x)

DecisionProcedure₂ : {i j k : Level} {A : Type i} {B : A → Type j} →
                     ((x : A) → B x → Type k) → Type (i ⊔ j ⊔ k)
DecisionProcedure₂ {A = A} {B = B} C = (x : A) (y : B x) → Decision (C x y)
```
