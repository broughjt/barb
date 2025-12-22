#import("../../../../../library/template.typ"): *

#show: template

```agda
module Base.Function.Core where

open import Base.Universe.Core
```

= Identity function <note:efea6413-096d-4249-8ef0-a4de74fcee13>

For any type $A$, the *identity function* on $A$, written $id_(A) ofType A -> A$,
takes its argument and returns it unchanged @rijke2025[def. 2.2.3]
@aluffi2009[9].

```agda
identity : {i : Level} {A : Type i} → A → A
identity x = x
```

= Constant function <note:11168612-1fca-405d-b3c5-2ecb0ece3521>

Given a fixed element $y ofType B$, the *constant function*, written
$constant_(y) ofType A -> B$ ignores its argument and returns $y$
@rijke2025[exer. 2.3].

```agda
constant : {i j : Level} {A : Type i} {B : Type j} → B → A → B
constant y _ = y
```

= Function composition <note:bc9568f6-830b-4b4e-9aab-1808b1127cb0>

Let $A$ be a type, let $B$ be a
#link("note://b05d0e2e-b6ab-45ab-9277-9559f4ee5e1f")[family over] $A$, and let
$C$ be a family indexed by $x ofType A$ and $y ofType B(x)$. Given functions

$
    f ofType piType(x, A) B(x) quad "and" quad g ofType piType(y, B(x)) C(x, y),
$

the *composition* of $g$ after $f$ is a new function $g compose f ofType
piType(x, A) C(x, f(x))$ given by

$
    (g compose f)(x) := g(f(x))
$

which applies $f$ to $x ofType A$ and then applies $g$ to the result to get
$g(f(x)) ofType C(x, f(x))$ @rijke2025[def. 2.2.5].

```agda
_∘_ : {i j k : Level}
      {A : Type i} {B : A → Type j} {C : {x : A} → B x → Type k} →
      ({x : A} → (y : B x) → C y) → (f : (x : A) → B x) →
      ((x : A) → C (f x))
(g ∘ f) x = g (f x)

infixr 9 _∘_
```

= Flip function <note:c13b9cdf-5f6c-4496-85b4-5dc64e342097>
 
The *flip* function takes a (curried) two-input function and flips the order of
its arguments @rijke2025[exer.~2.4(a)].

```agda
flip : {i j k : Level} {A : Type i} {B : Type j} {C : A → B → Type k} →
       ((x : A) (y : B) → C x y) → ((y : B) (x : A) → C x y)
flip f y x = f x y
```

The output type may depend on the two input arguments, but since their order is
swapped, the two input types $A$ and $B$ do not depend on each other.

= Function application syntax sugar <note:58a05cac-0621-4582-86ed-7c34a52ddcdf>
 
Haskell as a right-associative infix application operator `$` for avoiding the
use of parentheses which we duplicate here.

```agda
_$_ : {i j : Level} {A : Type i} {B : A → Type j} →
      ((x : A) → B x) → (x : A) → B x
f $ x = f x

infixr -1 _$_
```

= Flipped function application syntax sugar (pipe-forward) <note:ac0a22e1-3510-4129-ab02-d0f95da4a48c>

Haskell has a pipe forward application infix operator which takes an element
first and a function second and applies the function to the element. We define
it here as the #link("note://c13b9cdf-5f6c-4496-85b4-5dc64e342097")[flipped]
version of the `$`
#link("note://58a05cac-0621-4582-86ed-7c34a52ddcdf")[application operator].

```agda
_|>_ : {i j : Level} {A : Type i} {B : A → Type j} →
       (x : A) → ((x : A) → B x) → B x
_|>_ = flip _$_

infixl 0 _|>_
```
