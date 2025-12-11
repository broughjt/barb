#import("../../../../../library/template.typ"): *

#show: template

```agda
module Base.Identity.Definitions where

open import Base.Function.Negation
open import Base.Identity.Core
open import Base.Universe
```

= Disequality <note:3cb5f252-202d-45a6-a77f-c7db57262632>

Given a type $A$ and elements $x, y ofType A$, we define *disequality* between
$x$ and $y$, written $x != y$, as the
#link("note://16ffba35-7712-4eb7-8902-0812e529aa16")[negation] of the
#link("note://261490cb-2887-4247-9a83-7f674e3c9651")[identity type] $x = y$
@univalentfoundationsprogram2013[sec. 1.12.3].

```agda
_≠_ : {i : Level} {A : Type i} → A → A → Type i
x ≠ y = ¬ x ＝ y

infix 4 _≠_
```

When $x != y$ holds, we say $x$ and $y$ are *unequal* or *not equal*. We refer
to $!=$ as "disequality" because the term "inequality" is traditionally reserved
for relations which constitute a strict or non-strict partial order.
