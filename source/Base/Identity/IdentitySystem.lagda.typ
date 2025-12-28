#import("../../../../../library/template.typ"): *

#show: template

```agda
module Base.Identity.IdentitySystem where

open import Base.Function.Definitions
open import Base.Identity.Core
open import Base.Universe.Core
```

= Identity system <note:f349b4cc-b6bb-433a-be57-9f2a3d9d8757>
 
We follow #cite(<rijke2025>, form: "prose", supplement: "def 11.2.1") for the
following definition.

Let $A$ be a type equipped with an element $a ofType A$. A *(unary) identity
system* on $A$ at $a$ consists of a
#link("note://b05d0e2e-b6ab-45ab-9277-9559f4ee5e1f")[type family] $B$ over $A$
equipped with a $b ofType B(a)$ such that for any family of types $P(x, y)$
indexed by $x ofType A$ and $y ofType B(x)$, the function
$
    lambda h . h(a, b) ofType (piType(x, A) piType(y, B(x)) P(x, y)) -> P(a, b)
$
has a #link("note://32c2ca55-63ba-411b-9052-676a51fd16a1")[section].

In other words, if $B$ is an identity system on $A$ at $a$ and $P$ is a family
of types indexed by $x ofType A$ and $y ofType B(x)$, then there is a function
$
    f ofType P(a, b) -> (piType(x, A) piType(y, B(x)) P(x, y))
$

such that for each $p ofType P(a, b)$, there is a path $f(a, b) = p$. Viewed
this way, identity systems can be viewed as a generalization of
#link("note://261490cb-2887-4247-9a83-7f674e3c9651")[path induction] in much the
same way that #link("note://2a65336f-3db1-411e-869f-9c87a18d408a")[singleton
induction] is a generalization of the
#link("note://fe0ba530-46e9-4031-83bb-330db4d12b4e")[induction principle of the
unit type].

```agda
IdentitySystem :
  {i j k : Level}
  (A : Type i) (a : A)
  (B : A → Type j) → B a →
  Type (i ⊔ j ⊔ successor k)
IdentitySystem {k = k} A a B b =
  (P : (x : A) → B x → Type k) →
  Section (λ (h : (x : A) → (y : B x) → P x y) → h a b)
```
