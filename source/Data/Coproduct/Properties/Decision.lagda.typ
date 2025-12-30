#import("../../../../../../library/template.typ"): *

#show: template

```agda
module Data.Coproduct.Properties.Decision where

open import Base.Decision.Core
open import Base.Decision.Definitions
open import Base.Decision.Properties
open import Base.Function.Core
open import Base.Function.Properties.Equivalence
open import Base.Universe.Core
open import Base.Universe.Properties.Lift
open import Data.Coproduct.Core
open import Data.Coproduct.Definitions as Coproduct
open import Data.Coproduct.Properties.Identity
open import Data.Sigma.Core
open import Data.Sigma.Definitions as Sigma
```

= Necessary and sufficient conditions for decidable equality of a coproduct type <note:bbbe627b-db61-4056-832e-0f6ce72311a5>
 
#lemma(supplement: cite_link(<rijke2025>, "Rijke 2025, exer. 8.7(b)"))[
    For all types $A$ and $B$, the coproduct type $A + B$ has decidable equality
    if and only if both $A$ and $B$ have decidable equality.
]

The proof is analogous to that of
#link("note://938799fe-67a3-4a5c-87d8-625983fc9b57")[Lemma 55], except here of
course we use the
#link("note://d30c9670-8903-4e87-8234-c463ce37ad88")[characterization of
coproduct identity types].

```agda
＋-decide-＝→decide-＝₁ :
  {i j : Level} {A : Type i} {B : Type j} →
  Decide-＝ (A ＋ B) → Decide-＝ A
＋-decide-＝→decide-＝₁ d x x' =
  ↔-decide→decide (≃→↔ (＝≃Equal₁₁ x x')) (d (inject₁ x) (inject₁ x'))

＋-decide-＝→decide-＝₂ :
  {i j : Level} {A : Type i} {B : Type j} →
  Decide-＝ (A ＋ B) → Decide-＝ B
＋-decide-＝→decide-＝₂ d y y' =
  ↔-decide→decide (≃→↔ (＝≃Equal₂₂ y y')) (d (inject₂ y) (inject₂ y'))

decide-＝→＋-decideEqual :
  {i j : Level} {A : Type i} {B : Type j} →
  Decide-＝ A → Decide-＝ B →
  DecisionProcedure₂ $ Coproduct.Equal {A = A} {B = B}
decide-＝→＋-decideEqual d₁ d₂ (inject₁ x) (inject₁ x') =
  ↔-decide→decide lift↔ (d₁ x x')
decide-＝→＋-decideEqual d₁ d₂ (inject₁ x) (inject₂ y') =
  ↔-decide→decide lift↔ decide-𝟎
decide-＝→＋-decideEqual d₁ d₂ (inject₂ y) (inject₁ x') =
  ↔-decide→decide lift↔ decide-𝟎
decide-＝→＋-decideEqual d₁ d₂ (inject₂ y) (inject₂ y') =
  ↔-decide→decide lift↔ (d₂ y y')

decide-＝→＋-decide-＝ :
  {i j : Level} {A : Type i} {B : Type j} →
  Decide-＝ A → Decide-＝ B →
  Decide-＝ (A ＋ B)
decide-＝→＋-decide-＝ d₁ d₂ u v =
  ↔-decide→decide
    (Sigma.swap $ ＝↔Equal u v)
    (decide-＝→＋-decideEqual d₁ d₂ u v)
```
