#import("../../../../../library/template.typ"): *

#show: template

```agda
module Data.Coproduct.Core where

open import Base.Universe
```

= Coproduct type <note:001d31c7-7fb6-4878-883a-ff464bb9c0a8>

Given types $A$ and $B$, the *coproduct* $A + B$ is an
#link("note://367095ff-9cce-417f-a059-9c0290d0ca99")[inductive type] with
#link("note://367095ff-9cce-417f-a059-9c0290d0ca99")[constructors]

$
    inject1 & ofType A -> A + B, \
    inject2 & ofType B -> A + B
$

satisfying the #link("note://367095ff-9cce-417f-a059-9c0290d0ca99")[induction
principle] that for any
#link("note://b05d0e2e-b6ab-45ab-9277-9559f4ee5e1f")[family of types] $P(u)$
indexed by $u ofType A + B$, there is a function

$
    induction_(+) ofType ( piType(x, A) P(inject1(x)) ) ->
    ( piType(y, B) P(inject2(y)) ) -> piType(u, A + B) P(u)
$

such that the #link("note://367095ff-9cce-417f-a059-9c0290d0ca99")[computation
rules]

$
    induction_(+)(f, g, inject1(x)) & dot(eq) f(x), \
    induction_(+)(f, g, inject2(y)) & dot(eq) g(y)
$

hold @rijke2025[def.~4.4.1].

```agda
data _＋_ {i j : Level} (A : Type i) (B : Type j) : Type (i ⊔ j) where
  inject₁ : A → A ＋ B
  inject₂ : B → A ＋ B

infixl 1 _＋_

induction : {i j k : Level} {A : Type i} {B : Type j} {P : A ＋ B → Type k} →
            ((x : A) → P (inject₁ x)) → ((y : B) → P (inject₂ y)) →
            ((u : A ＋ B) → P u)
induction f g (inject₁ x) = f x
induction f g (inject₂ y) = g y

recursion : {i j k : Level} {A : Type i} {B : Type j} {C : Type k} →
            (A → C) → (B → C) → (A ＋ B → C)
recursion = induction
```
