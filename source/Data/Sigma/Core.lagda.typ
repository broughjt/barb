#import("../../../../../library/template.typ"): *

#show: template

```agda
module Data.Sigma.Core where

open import Base.Function.Core
open import Base.Universe
```

= Sigma type <note:ae098784-7572-4d29-b548-a2db9b6d004a>
 
Given a #link("note://b05d0e2e-b6ab-45ab-9277-9559f4ee5e1f")[type family] $B$
over $A$, the *dependent pair type* (or *$Sigma$-type*), written $sigmaType(x,
A) B(x)$, is an #link("note://367095ff-9cce-417f-a059-9c0290d0ca99")[inductive
type] equipped with a *pairing*
#link("note://367095ff-9cce-417f-a059-9c0290d0ca99")[constructor]
$
    pair ofType piType(x, A) ( B(x) -> sigmaType(y, A) B(y) )
$
@rijke2025[def. 4.6.1].  The
#link("note://367095ff-9cce-417f-a059-9c0290d0ca99")[induction principle] for
$Sigma$-types asserts for any
#link("note://b05d0e2e-b6ab-45ab-9277-9559f4ee5e1f")[type family] $P(u)$ indexed
by $u ofType sigmaType(x, A) B(x)$, there is a function
$
    induction_(Sigma) ofType ( piType(x, A) piType(y, B(x)) P(pair(x, y)) ) ->
    ( piType(u, sigmaType(x, A) B(x)) P(u) )
$
such that the #link("note://367095ff-9cce-417f-a059-9c0290d0ca99")[computation
rule]
$
    induction_(Sigma)(f, pair(x, y)) dot(eq) f(x, y)
$
holds.

```agda
data Σ {i j : Level} (A : Type i) (B : A → Type j) : Type (i ⊔ j) where
  pair : (x : A) → B x → Σ A B

induction : {i j k : Level}
            {A : Type i} {B : A → Type j} {P : Σ A B → Type k} →
            ((x : A) (y : B x) → P $ pair x y) → ((u : Σ A B) → P u)
induction f (pair x y) = f x y

recursion : {i j k : Level}
            {A : Type i} {B : A → Type j} {C : Type k} →
            ((x : A) → B x → C) → (Σ A B → C)
recursion = induction
```

There are *projection maps* which return the first and second components of a
$Sigma$-type @rijke2025[def. 4.6.2]. The *first projection map* is a function
$
    project1 ofType sigmaType(x, A) B(x) -> A
$
is defined by induction (pattern matching) as
$
    project1(x, y) := x.
$
The *second projection map* is a dependent function
$
    project2 ofType piType(u, sigmaType(x, A) B(x)) B(project1(u) )
$
defined by induction (pattern matching) as
$
    project2(x, y) := y.
$
Crucially, the codomain type for the second projection
depends on the value of the first projection of $u$.

```agda
project₁ : {i j : Level} {A : Type i} {B : A → Type j} →
           Σ A B → A
project₁ (pair x _) = x

project₂ : {i j : Level} {A : Type i} {B : A → Type j} →
           (u : Σ A B) → B $ project₁ u
project₂ (pair _ y) = y
```

= (Cartesian) Product type <note:23a01b78-e433-4a66-8915-bfda82ee149a>
 
Given types $A$ and $B$, the *product type* $A times B$ of $A$ and $B$ is
defined by
$
    A times B := sigmaType(x, A) B.
$

The product type is a special case of a
#link("note://ae098784-7572-4d29-b548-a2db9b6d004a")[$Sigma$-type], where the
#link("note://b05d0e2e-b6ab-45ab-9277-9559f4ee5e1f")[type family] $B(x)$ is
constant over $A$.

```agda
_×_ : {i j : Level} (A : Type i) (B : Type j) → Type (i ⊔ j)
A × B = Σ A (constant B)
```
