#import("../../../../../library/template.typ"): *

#show: template

```agda
module Data.Bool.Properties where

open import Base.Decision.Core
open import Base.Decision.Definitions
open import Base.Decision.Properties
open import Base.Family.Definitions
open import Base.Family.Properties
open import Base.Function.Core
open import Base.Function.Definitions hiding (_∙_; _⁻¹)
open import Base.Function.Negation
open import Base.Function.Properties.Equivalence
open import Base.Identity.Core
open import Base.Identity.Definitions
open import Base.Identity.Properties
open import Base.Universe.Core
open import Data.Bool.Core as Bool
open import Data.Bool.Definitions as Bool
open import Data.Empty as Empty
open import Data.Sigma.Core
open import Data.Unit.Core as Unit
```

= Observational equality on booleans is reflexive <note:4793b3c0-efaf-4823-897e-b035568ee6bb>
 
#lemma(label: "14")[
    #link("note://3a2749a4-1b34-4bd5-8821-271a987b029a")[Observational equality
    on booleans] is
    #link("note://7e7a1c6f-6051-4526-83e9-01d030717ea5")[reflexive].
]
#proof[
    Use the #link("note://78e3004d-88e7-45e5-8d4d-da76962195f3")[induction
    principle for booleans] and the
    #link("note://3a2749a4-1b34-4bd5-8821-271a987b029a")[definition of
    observational equality].
]

```agda
equalReflexive : Reflexive Equal
equalReflexive false = ⋆
equalReflexive true = ⋆
```

= Boolean observational equality is logically equivalent to equality <note:be8adac5-28fe-4666-af31-b5050c2454ac>
 
#lemma(
    label: "16",
    supplement: cite_link(<rijke2025>, "Rijke 2025, exer. 6.2(b)")
)[
    For #link("note://78e3004d-88e7-45e5-8d4d-da76962195f3")[booleans] $x$ and
    $y$, if is an
    #link("note://261490cb-2887-4247-9a83-7f674e3c9651")[identification] $x = y$
    if and only if $x$ and $y$ are
    #link("note://3a2749a4-1b34-4bd5-8821-271a987b029a")[observationally equal].
]
#proof[
    For the ($==>$) direction, use the
    #link("note://9d7cf197-7f2a-4633-aa63-1c9df1429a13")[empty type] and
    #link("note://78e3004d-88e7-45e5-8d4d-da76962195f3")[boolean] induction
    principles.

    For the converse ($<==$), use
    #link("note://d25ccc40-b51e-466f-b87a-59be3acfa38a")[Lemma 11] (which gives
    a canonical map from identity types into
    #link("note://7e7a1c6f-6051-4526-83e9-01d030717ea5")[reflexive] type
    families) together with
    #link("note://4793b3c0-efaf-4823-897e-b035568ee6bb")[Lemma 14] (which shows
    that observational equality on booleans is reflexive).
]

```agda
Equal→＝ : {x y : 𝟐} → Equal x y → x ＝ y
Equal→＝ {false} {false} e = reflexive
Equal→＝ {true} {true} e = reflexive

＝→Equal : {x y : 𝟐} → x ＝ y → Equal x y
＝→Equal {x} {x} reflexive = equalReflexive x

Equal↔＝ : {x y : 𝟐} → Equal x y ↔ (x ＝ y)
Equal↔＝ = pair Equal→＝ ＝→Equal
```

= Boolean double negation homotopic to identity <note:547845e0-625b-4444-9b32-9a66352293d2>
 
#lemma(
    label: "19",
    supplement: cite_link(<rijke2025>, "Rijke 2025, ex. 9.1.3")
)[
    There is a #link("note://3cb1b8ca-2a77-4c8a-b726-ed8f10dfd208")[homotopy]
    $
        (lambda x . ! x) compose (lambda x . ! x) ~ id_(Bool)
    $
    between double #link("note://84ca1018-8448-4ecf-beb0-9bc92b18c914")[boolean
    negation] and the
    #link("note://efea6413-096d-4249-8ef0-a4de74fcee13")[identiy map].

    In other words, negation is an
    #link("note://47767cc9-0064-45d3-8735-203b3236976d")[involution].
]
#proof[
    The cases for both $btrue$ and $bfalse$ hold
    #link("note://84ca1018-8448-4ecf-beb0-9bc92b18c914")[definitionally].
]

```agda
!!∼identity : (!_ ∘ !_) ∼ identity
!!∼identity false = reflexive
!!∼identity true = reflexive

!-involutive : Involutive !_
!-involutive = pair !!∼identity !!∼identity
```

See #link("note://78e3004d-88e7-45e5-8d4d-da76962195f3")[Type of booleans].

= Boolean observational equality is decidable <note:2049243a-0a64-4454-a979-2e122082f470>
 
#lemma(label: "15")[
    #link("note://3a2749a4-1b34-4bd5-8821-271a987b029a")[Observational equality
    on booleans] is
    #link("note://36f1a370-ca8c-4053-8ee6-d284b50b90e5")[decidable].
]
#proof[
    Use the #link("note://78e3004d-88e7-45e5-8d4d-da76962195f3")[induction
    principle for booleans], the
    #link("note://3a2749a4-1b34-4bd5-8821-271a987b029a")[definition of
    observational equality], and the decidablity of the
    #link("note://f5e3fd77-76be-4ea5-8325-8e6b6d91442a")[empty] and
    #link("note://cd708a57-9e0d-4bac-b7d9-2ad14883d7f4")[unit] types.
]

```agda
decideEqual : DecisionProcedure₂ Equal
decideEqual false false = decide-𝟏
decideEqual false true = decide-𝟎
decideEqual true false = decide-𝟎
decideEqual true true = decide-𝟏
```

= Booleans have decidable equality <note:2ac7b4ea-297d-4cdb-a6b3-196677bbc504>
 
#lemma[
    #link("note://78e3004d-88e7-45e5-8d4d-da76962195f3")[Booleans] have
    #link("note://b7fff70f-d736-440d-bd2c-a827baef5171")[decidable equality].
]
#proof[
    We showed in #link("note://2049243a-0a64-4454-a979-2e122082f470")[Lemma 15]
    that #link("note://3a2749a4-1b34-4bd5-8821-271a987b029a")[boolean
    observational equality] is
    #link("note://36f1a370-ca8c-4053-8ee6-d284b50b90e5")[decidable], and by
    #link("note://be8adac5-28fe-4666-af31-b5050c2454ac")[Lemma 16] observational
    equality is logically equivalent to identity for booleans, so it follows by
    #link("note://d70b37f9-d122-414e-98b2-19ac5af7a159")[Lemma 17] that booleans
    have decidable equality.
]

```agda
decide-＝ : Decide-＝ 𝟐
decide-＝ x y = ↔-decide→decide Equal↔＝ (decideEqual x y)
```

= Boolean negate not equal <note:3f7dcf4e-a842-48c6-9268-07e1327d79b6>
 
#lemma(
    label: "18",
    supplement: cite_link(<rijke2025>, "Rijke 2025, exer. 6.2(c)")
)[
    For all #link("note://78e3004d-88e7-45e5-8d4d-da76962195f3")[booleans] $b$,
    $! b != b$.
]
#proof[
    If $bfalse = btrue$ or $btrue = bfalse$, we can use
    #link("note://be8adac5-28fe-4666-af31-b5050c2454ac")[the logical equivalence
    of observational equality and identity on booleans] to obtain
    contradictions.
]

```agda
!≠ : (b : 𝟐) → (! b) ≠ b
!≠ false = Empty.recursion ∘ ＝→Equal
!≠ true = Empty.recursion ∘ ＝→Equal
```

= Boolean false not equal true <note:81b4941d-2637-4409-b580-9f430a10d918>

#lemma(supplement: cite_link(<rijke2025>, "Rijke 2025, exer. 6.2(c)"))[
    We have $bfalse != btrue$.
]
#proof[
    Apply #link("note://3f7dcf4e-a842-48c6-9268-07e1327d79b6")[Lemma 18] to
    $btrue$.
]

See #link("note://78e3004d-88e7-45e5-8d4d-da76962195f3")[Type of booleans].

```agda
false≠true : false ≠ true
false≠true = !≠ true
```

= Boolean negation is an equivalence <note:c123b258-a8c7-4ea1-812c-8c6fbbd83844>
 
#lemma(supplement: cite_link(<rijke2025>, "Rijke 2025, ex. 9.2.4"))[
    #link("note://78e3004d-88e7-45e5-8d4d-da76962195f3")[Boolean]
    #link("note://84ca1018-8448-4ecf-beb0-9bc92b18c914")[negation] is an
    #link("note://32c2ca55-63ba-411b-9052-676a51fd16a1")[equivalence].
]
#proof[
    Follows from #link("note://547845e0-625b-4444-9b32-9a66352293d2")[Lemma 19],
    which shows that negation is
    #link("note://47767cc9-0064-45d3-8735-203b3236976d")[involutive].
]

```agda
!-equivalence : IsEquivalence !_
!-equivalence = inverse→isEquivalence !_ !_ !-involutive
```

= Constant function on booleans is not an equivalence <note:959b4539-5474-40a9-b7ae-bf439f91f68d>

#lemma(supplement: cite_link(<rijke2025>, "Rijke 2025, exer. 9.2(a)"))[
    For each $b ofType Bool$, the
    #link("note://11168612-1fca-405d-b3c5-2ecb0ece3521")[constant function]
    $constant_(b) ofType Bool -> Bool$ is not an
    #link("note://32c2ca55-63ba-411b-9052-676a51fd16a1")[equivalence].
]
#proof[
    Let $b ofType Bool$ and suppose for contradiction that $constant_(b) ofType
    Bool -> Bool$ is an equivalence. Then in particular, $constant_(b)$ has a
    #link("note://32c2ca55-63ba-411b-9052-676a51fd16a1")[section]---that is,
    there is a function $f ofType Bool -> Bool$ equipped with a
    #link("note://3cb1b8ca-2a77-4c8a-b726-ed8f10dfd208")[homotopy] $H ofType
    constant_(b) compose f ~ id_(Bool)$. Appy $H$ to $! b$. This gives a
    #link("note://261490cb-2887-4247-9a83-7f674e3c9651")[path]
    $
        b = ! b,
    $
    but this is a contradiction by
    #link("note://3f7dcf4e-a842-48c6-9268-07e1327d79b6")[Lemma 18], which shows
    that $! b = b$ never holds.
]

```agda
constantNotEquivalence : (b : 𝟐) →
                         ¬ IsEquivalence (constant {A = 𝟐} b)
constantNotEquivalence b (pair (pair f H) (pair g K)) =
  absurd (K $ ! b) (≠-symmetric (!≠ b))
```

= Booleans not equivalent to the unit type <note:71caa6f0-5e7e-4cd6-9564-1566e2021c79>
 
#lemma(supplement: cite_link(<rijke2025>, "Rijke 2025, exer. 9.2(b)"))[
    The #link("note://78e3004d-88e7-45e5-8d4d-da76962195f3")[booleans] are not
    #link("note://32c2ca55-63ba-411b-9052-676a51fd16a1")[equivalent] to the
    #link("note://fe0ba530-46e9-4031-83bb-330db4d12b4e")[unit type].
]
#proof[
    Suppose for contradiction that there is an
    #link("note://32c2ca55-63ba-411b-9052-676a51fd16a1")[equivalence] $f ofType
    Bool -> unitType$. Then there are two functions $g, h ofType unitType ->
    Bool$ and #link("note://3cb1b8ca-2a77-4c8a-b726-ed8f10dfd208")[homotopies]
    $
        G ofType & f compose g ∼ id_(Bool), \
        H ofType & g compose f ~ id_(unitType).
    $
    Apply $H$ to the
    #link("note://84ca1018-8448-4ecf-beb0-9bc92b18c914")[negation] $!
    h(star)$. This gives a
    #link("note://261490cb-2887-4247-9a83-7f674e3c9651")[path]
    $
        h(f(! h(star))) = ! h(star).
    $
    However, if we apply the
    #link("note://fe0ba530-46e9-4031-83bb-330db4d12b4e")[induction principle for
    the unit type] with the
    #link("note://b05d0e2e-b6ab-45ab-9277-9559f4ee5e1f")[family] $P(x) := h(x) =
    h(star)$ indexed by $x ofType unitType$ to the value $f(! h(x))$, we obtain
    a path
    $
        h(f(! h(star))) = h(star).
    $
    #link("note://984d4510-34b9-492f-a792-95a19117193e")[Concatenating] the
    #link("note://95e3c813-ae44-4341-ac56-286cda078568")[inverse] of the first
    path with the second gives $! h(star) = h(star)$, which is a contradiction
    by #link("note://3f7dcf4e-a842-48c6-9268-07e1327d79b6")[Lemma 18].
]

```agda
bool≄unit : ¬ (𝟐 ≃ 𝟏)
bool≄unit (pair f (pair (pair g G) (pair h H))) = 
  absurd (p ⁻¹ ∙ q) (!≠ (g ⋆))
  where
  p : g (f (! g ⋆)) ＝ (! g ⋆)
  p = G $ ! (g ⋆)

  q : g (f (! g ⋆)) ＝ g ⋆
  q = Unit.induction {P = λ x → g x ＝ g ⋆} reflexive (f (! g ⋆))
```
