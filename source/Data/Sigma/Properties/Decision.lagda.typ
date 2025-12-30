#import("../../../../../../library/template.typ"): *

#show: template

```agda
module Data.Sigma.Properties.Decision where

open import Base.Decision.Core
open import Base.Decision.Definitions
open import Base.Decision.Properties
open import Base.Function.Core
open import Base.Function.Definitions
open import Base.Function.Negation
open import Base.Function.Properties.Equivalence
open import Base.Identity.Core
open import Base.Universe.Core
open import Data.Coproduct.Core
open import Data.Coproduct.Definitions as Coproduct
open import Data.Sigma.Core
open import Data.Sigma.Definitions as Sigma
open import Data.Sigma.Properties.Identity
```

= Necessary and sufficient condition for decidable equality of a product type <note:938799fe-67a3-4a5c-87d8-625983fc9b57>
 
#lemma(
    label: "55",
    supplement: cite_link(<rijke2025>, "Rijke 2025, exer. 8.6")
)[
    Let $A$ and $B$ be types. The
    #link("note://23a01b78-e433-4a66-8915-bfda82ee149a")[product] $A times B$
    has #link("note://b7fff70f-d736-440d-bd2c-a827baef5171")[decidable equality]
    if and only if there are functions
    $
        B -> sans("DecidableEquality")(A), \
        A -> sans("DecidableEquality")(B).
    $
]
#proof[
    ($==>$) Suppose $A times B$ has decidable equality, with a
    #link("note://36f1a370-ca8c-4053-8ee6-d284b50b90e5")[decision procedure]
    $
        d_(A times B) ofType piType(u, v, A times B) Decision(u = v).
    $
    We construct functions
    $
        B -> piType(x, x', A) Decision(x = x'), \
        A -> piType(y, y', B) Decision(y = y').
    $

    To define the first function, fix $y ofType B$ and $x, x' ofType
    A$. Applying $d_(A times B)$ to the pairs $(x, y)$ and $(x, x')$ yields a
    #link("note://36f1a370-ca8c-4053-8ee6-d284b50b90e5")[decision]
    $
        Decision((x, y) = (x', y)).
    $
    By the #link("note://dbc89e73-b38a-49b8-b20e-06a10e62393b")[characterization
    of the identity types of products], we have a
    #link("note://27061ddb-2091-46c1-8752-21db2ab57f44")[logical equivalence]
    $
        ((x, y) = (x', y)) <==> x = x'.
    $
    By #link("note://d70b37f9-d122-414e-98b2-19ac5af7a159")[Lemma 17],
    decidability is preserved by logical equivalence, so we obtain a decision
    of $x = x'$. This defines a function $B -> sans("DecidableEquality")(A)$.

    The construction of the second function is analogous, fixing $x ofType A$
    and comparing pairs of the form $(x, y)$ and $(x, y')$.

    ($<==$) Conversely, suppose we have functions
    $
        d_(A) ofType B -> piType(x, x', A) Decision(x = x'), \
        d_(B) ofType A -> piType(y, y', B) Decision(y = y').
    $
    We construct a decision procedure
    $
        d_(A times B) ofType piType(u, v, A times B) Decision(u = v).
    $

    Fix $(x, y), (x', y') ofType A times B$. Applying the given decision
    procedures yields decisions
    $
        Decision(x = x') quad "and" quad Decision(y = y')
    $
    By #link("note://244cf793-6456-4035-9bf5-236bfec8ceb5")[Lemma 54], it
    follows that there is a decision
    $
        Decision((x = x') times (y = y')).
    $
    Using the
    #link("note://dbc89e73-b38a-49b8-b20e-06a10e62393b")[characterization of the
    identity types of products], we have a logical equivalence
    $
        (x = x') times (y = y') <==> (x, y) = (x', y')
    $
    Applying #link("note://d70b37f9-d122-414e-98b2-19ac5af7a159")[Lemma 17] once
    more, we obtain a decision of $(x, y) = (x', y')$ as required.
]

```agda
×-decide-＝→inhabited→decide-＝₁ :
  {i j : Level} {A : Type i} {B : Type j} →
  Decide-＝ (A × B) →
  (B → Decide-＝ A)
×-decide-＝→inhabited→decide-＝₁ d y x x' =
  ↔-decide→decide
    (p ∘↔ ＝↔Equal-× (pair x y) (pair x' y))
    (d (pair x y) (pair x' y))
  where
  p : Equal-× (pair x y) (pair x' y) ↔ x ＝ x'
  p = pair project₁ (flip pair reflexive)

×-decide-＝→inhabited→decide-＝₂ :
  {i j : Level} {A : Type i} {B : Type j} →
  Decide-＝ (A × B) →
  (A → Decide-＝ B)
×-decide-＝→inhabited→decide-＝₂ d x y y' =
  ↔-decide→decide
    (p ∘↔ ＝↔Equal-× (pair x y) (pair x y'))
    (d (pair x y) (pair x y'))
  where
  p : Equal-× (pair x y) (pair x y') ↔ y ＝ y'
  p = pair project₂ (pair reflexive)

inhabited→decide-＝→×-decideEqual-× :
  {i j : Level} {A : Type i} {B : Type j} →
  (B → Decide-＝ A) →
  (A → Decide-＝ B) →
  DecisionProcedure₂ $ Equal-× {A = A} {B = B}
inhabited→decide-＝→×-decideEqual-× d₁ d₂ (pair x y) (pair x' y') =
  decide-× (d₁ y x x') (d₂ x y y')

inhabited→decide-＝→×-decide-＝ :
  {i j : Level} {A : Type i} {B : Type j} →
  (B → Decide-＝ A) →
  (A → Decide-＝ B) →
  Decide-＝ (A × B)
inhabited→decide-＝→×-decide-＝
  d₁ d₂ u v =
  ↔-decide→decide
    (Sigma.swap (＝↔Equal-× u v))
    (inhabited→decide-＝→×-decideEqual-× d₁ d₂ u v)

×-decide-＝→inhabited→decide-＝ :
  {i j : Level} {A : Type i} {B : Type j} →
  Decide-＝ (A × B) ↔ ((B → Decide-＝ A) × (A → Decide-＝ B))
×-decide-＝→inhabited→decide-＝ =
  pair
    (Sigma.map
      ×-decide-＝→inhabited→decide-＝₁
      ×-decide-＝→inhabited→decide-＝₂ ∘
     (λ p → pair p p))
    (uncurry inhabited→decide-＝→×-decide-＝)

decide-＝→×-decideEqual-× :
  {i j : Level} {A : Type i} {B : Type j} →
  Decide-＝ A →
  Decide-＝ B →
  DecisionProcedure₂ $ Equal-× {A = A} {B = B}
decide-＝→×-decideEqual-× d₁ d₂ =
  inhabited→decide-＝→×-decideEqual-× (constant d₁) (constant d₂)

decide-＝→×-decide-＝ :
  {i j : Level} {A : Type i} {B : Type j} →
  Decide-＝ A →
  Decide-＝ B →
  Decide-＝ (A × B)
decide-＝→×-decide-＝ d₁ d₂ =
  inhabited→decide-＝→×-decide-＝ (constant d₁) (constant d₂)
```
