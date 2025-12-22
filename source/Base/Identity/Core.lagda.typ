#import("../../../../../library/template.typ"): *

#show: template

```agda
module Base.Identity.Core where

open import Base.Universe.Core
```

= Identity type <note:261490cb-2887-4247-9a83-7f674e3c9651>

Following #cite(<rijke2025>, form: "prose", supplement: "def. 5.1.1"), the
*identity type* of a type $A$ at an element $a ofType A$ an
#link("note://367095ff-9cce-417f-a059-9c0290d0ca99")[inductive]
#link("note://b05d0e2e-b6ab-45ab-9277-9559f4ee5e1f")[family of types] $a
attach(eq, br: A) x$ indexed by $x ofType A$, equipped with the
#link("note://367095ff-9cce-417f-a059-9c0290d0ca99")[constructor]
$
    refl_(a) ofType a attach(eq, br: A) a.
$
The #link("note://367095ff-9cce-417f-a059-9c0290d0ca99")[induction principle]
for the identity type asserts that for any family of types $P(x, p)$ indexed by
$x ofType A$ and $p ofType a attach(eq, br: A) x$, there is a function
$
    induction_(eq)^(a) ofType P(a, refl_(a)) ->
    piType(x, A) piType(p, a attach(eq, br: A) x) P(x, p)
$
which, given $u ofType P(a, refl_(a))$, satisfies the
#link("note://367095ff-9cce-417f-a059-9c0290d0ca99")[computation rule]
$
    induction_(eq)^(a)(u, a, refl_(a)) dot(eq) u.
$

An element of the identity type $a attach(eq, br: A) x$ is called an
identification of $a$ with $x$, or a *path* from $a$ to $x$. The induction
principle for identity types is also referred to as *identification elimination*
or *path induction*.

```agda
data _＝_ {i : Level} {A : Type i} (a : A) : A → Type i where
  reflexive : a ＝ a

infix 4 _＝_

induction : {i j : Level} {A : Type i} {a : A}
            {P : (x : A) (p : a ＝ x) → Type j} →
            P a reflexive → ((x : A) (p : a ＝ x) → P x p)
induction u a reflexive = u
```
