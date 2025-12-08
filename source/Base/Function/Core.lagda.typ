#import("../../../../../library/template.typ"): *

#show: template

```agda
module Base.Function.Core where

open import Base.Universe
```

= Identity function <note:efea6413-096d-4249-8ef0-a4de74fcee13>

For any type $A$, the *identity function* on $A$ takes its argument and returns
it unchanged @rijke2025[def. 2.2.3] @aluffi2009[9].

```agda
identity : {i : Level} {A : Type i} → A → A
identity x = x
```

= Constant function <note:11168612-1fca-405d-b3c5-2ecb0ece3521>

Given a fixed element $y ofType B$, the *constant function* ignores its argument and
returns $y$ @rijke2025[exer. 2.3].

```agda
constant : {i j : Level} {A : Type i} {B : Type j} → B → A → B
constant y _ = y
```

= Function composition <note:bc9568f6-830b-4b4e-9aab-1808b1127cb0>

Let $A$ be a type, let $B$ be a
#link("note://b05d0e2e-b6ab-45ab-9277-9559f4ee5e1f")[family over] $A$, and let
$C$ be a family indexed by $x ofType A$ and $y ofType B(x)$. Given functions

$
    f ofType piType(x, A) B(x) "and" g ofType piType(y, B(x)) C(x, y),
$

the *composition* of $g$ after $f$ is a new function $g compose f ofType
piType(x, A) C(x, f(x))$ given by

$
    (g compose f)(x) := g(f(x))
$

which applies $f$ to $x ofType A$ and then applies $g$ to the result to get
$g(f(x)) ofType C(x, f(x))$ @rijke2025[def. 2.2.5] @aluffi2009[10].

```agda
_∘_ : {i j k : Level}
      {A : Type i} {B : A → Type j} {C : {x : A} → B x → Type k} →
      ({x : A} → (y : B x) → C y) → (f : (x : A) → B x) →
      ((x : A) → C (f x))
(g ∘ f) x = g (f x)

infixr 9 _∘_
```
