#import("../../../../../library/template.typ"): *

#show: template

```agda
module Base.Truncation.Definitions where

open import Base.Function.Core
open import Base.Function.Definitions
open import Base.Identity.Core
open import Base.Universe.Core
open import Data.Sigma.Core
```

= Contractible type <note:f817901c-750e-4575-a259-d83730424ade>
 
Following #cite(<rijke2025>, form: "prose", supplement: "def. 10.1.1"), a type
$A$ is *contracitble* if it comes equipped with an element of type
$
    IsContractible(A) := sigmaType(c, A) piType(x, A) c = x.
$
Given a pair $(c, C) ofType IsContractible(A)$, we refer to $c ofType A$ as the
*center of contraction* of $A$, and we refer to $C ofType piType(x, A) c = x$ as
the *contraction* of $A$.

```agda
IsContractible : {i : Level} →
                 Type i → Type i
IsContractible A = Σ A (λ c → (x : A) → c ＝ x)
```

= Singleton induction <note:2a65336f-3db1-411e-869f-9c87a18d408a>
 
Following #cite(<rijke2025>, form: "prose", supplement: "def. 10.2.1"), a type
$A$ satisfies *singleton induction* if it comes equipped with an element $a
ofType A$ such that for every type family $B$ over $A$, the
#link("note://ac0a22e1-3510-4129-ab02-d0f95da4a48c")[evaluation map] at the
element $a$
$
    evaluate_(a) ofType ( piType(x, A) B(x) ) -> B(a),
$
given by $evaluate_(a)(f) := f(a)$, has a
#link("note://32c2ca55-63ba-411b-9052-676a51fd16a1")[section]. Expanding the
definition of a section, this means there is a map
$
    induction_(s)^(a) ofType B(a) -> ( piType(x, A) B(x) )
$
and a #link("note://3cb1b8ca-2a77-4c8a-b726-ed8f10dfd208")[homotopy]
$
    evaluate_(a) compose induction_(s)^(a) ~ id_(B(a)).
$

```agda
IsSingleton : {i j : Level} → (A : Type i) → Type (i ⊔ successor j)
IsSingleton {i} {j} A =
  Σ A (λ a → (B : A → Type j) → Section (_|>_ {A = A} {B = B} a))
```

Initially, I found this definition difficult to understand. The note
#link("note://5c363e12-3c53-4145-9b22-985fd2af9d7b")[Understanding the
definition of singleton induction] attempts to explain by drawing an analogy
with the situation for the
#link("note://fe0ba530-46e9-4031-83bb-330db4d12b4e")[unit type].

Note: I have slightly modified Rijke's definition by requiring the type $A$ to
be equipped with a distinguished element $a ofType A$ as part of the definition
of singleton induction, rather than treating its existence as a precondition.
