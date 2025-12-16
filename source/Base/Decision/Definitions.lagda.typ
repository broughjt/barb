#import("../../../../../library/template.typ"): *

#show: template

```agda
module Base.Decision.Definitions where

open import Base.Decision.Core
open import Base.Function.Core
open import Base.Function.Definitions
open import Base.Function.Negation
open import Base.Identity.Core
open import Base.Universe
open import Data.Bool.Core
open import Data.Bool.Definitions
open import Data.Coproduct.Core as Coproduct
open import Data.Empty as Empty
open import Data.Sigma.Core
open import Data.Unit as Unit
```

= Empty type is decidable <note:f5e3fd77-76be-4ea5-8325-8e6b6d91442a>
 
#lemma(supplement: cite_link(<rijke2025>, "ex. 8.1.2"))[
    The #link("note://9d7cf197-7f2a-4633-aa63-1c9df1429a13")[empty type]
    $emptyType$ is
    #link("note://36f1a370-ca8c-4053-8ee6-d284b50b90e5")[decidable].
]
#proof[
    The principle of recursion for the
    #link("note://9d7cf197-7f2a-4633-aa63-1c9df1429a13")[empty type] gives a
    function $not emptyType$.
]

```agda
decide-𝟎 : Decision 𝟎
decide-𝟎 = inject₂ Empty.recursion
```

= Unit type is decidable <note:cd708a57-9e0d-4bac-b7d9-2ad14883d7f4>
 
#lemma(supplement: cite_link(<rijke2025>, "ex. 8.1.2"))[
    The #link("note://fe0ba530-46e9-4031-83bb-330db4d12b4e")[unit type]
    $unitType$ is
    #link("note://36f1a370-ca8c-4053-8ee6-d284b50b90e5")[decidable].
]
#proof[
    Take $star ofType unitType$.
]

```agda
decide-𝟏 : Decision 𝟏
decide-𝟏 = inject₁ ⋆
```

= Decisions for products, coproducts, non-dependent function types, negations, and biconditionals <note:244cf793-6456-4035-9bf5-236bfec8ceb5>
 
#lemma(supplement: cite_link(<rijke2025>, "Rijke 2025, ex. 8.1.3"))[
    If two types $A$ and $B$ both have
    #link("note://36f1a370-ca8c-4053-8ee6-d284b50b90e5")[decisions], then there
    are also decisions for the types:

    - $A times B$
    - $A + B$
    - $A -> B$
    - $not A$
    - $A arrow.l.r B$
]
#proof[
    Use case analysis and the recursion principles for each type.
]

See #link("note://23a01b78-e433-4a66-8915-bfda82ee149a")[Product type],
#link("note://001d31c7-7fb6-4878-883a-ff464bb9c0a8")[Coproduct type],
#link("note://16ffba35-7712-4eb7-8902-0812e529aa16")[Negation of a type], and
#link("note://27061ddb-2091-46c1-8752-21db2ab57f44")[Logical biconditional].

```agda
decide-× : {i j : Level} {A : Type i} {B : Type j} →
           Decision A → Decision B → Decision (A × B)
decide-× (inject₁ x) (inject₁ y) = inject₁ $ pair x y
decide-× (inject₁ _) (inject₂ g) = inject₂ $ g ∘ project₂
decide-× (inject₂ f) _ = inject₂ $ f ∘ project₁

decide-＋ : {i j : Level} {A : Type i} {B : Type j} →
           Decision A → Decision B → Decision (A ＋ B)
decide-＋ (inject₁ x) _ = inject₁ $ inject₁ x
decide-＋ (inject₂ _) (inject₁ y) = inject₁ $ inject₂ y
decide-＋ (inject₂ f) (inject₂ g) = inject₂ $ Coproduct.recursion f g

decide-→ : {i j : Level} {A : Type i} {B : Type j} →
           Decision A → Decision B → Decision (A → B)
decide-→ (inject₁ _) (inject₁ y) = inject₁ $ constant y
decide-→ (inject₁ x) (inject₂ g) = inject₂ $ λ h → g (h x)
decide-→ (inject₂ f) y = inject₁ $ Empty.recursion ∘ f

decide-¬ : {i : Level} {A : Type i} →
           Decision A → Decision (¬ A)
decide-¬ = flip decide-→ decide-𝟎

decide-↔ : {i j : Level} {A : Type i} {B : Type j} →
           Decision A → Decision B → Decision (A ↔ B)
decide-↔ x y = decide-× (decide-→ x y) (decide-→ y x)
```

#cite(<rijke2025>, form: "prose", supplement: "ex. 8.1.3") notes that the proofs
for the decidability of products, coproducts, and non-dependent functions
correspond to the truth tables for logical conjunction, disjunction, and
implication in classical logic.

= Decidable equality <note:b7fff70f-d736-440d-bd2c-a827baef5171>
 
A type $A$ has *decidable equality* if it comes equipped with a
#link("note://b7fff70f-d736-440d-bd2c-a827baef5171")[decision procedure] for the
#link("note://b05d0e2e-b6ab-45ab-9277-9559f4ee5e1f")[family]
$
    piType(x, y, A) x attach(eq, br: A) y.
$
This is the same as saying that there is always a
#link("note://36f1a370-ca8c-4053-8ee6-d284b50b90e5")[decision] for the
#link("note://261490cb-2887-4247-9a83-7f674e3c9651")[identity type] $x
attach(eq, br: A) y$ between arbitrary elements $x, y$ of $A$.

```agda
DecidableEquality : {i : Level} → Type i → Type i
DecidableEquality A = DecisionProcedure₂ (λ (x y : A) → x ＝ y)
```

= Alternative decision combinators for products and function types <note:ead33018-a349-4cd6-a398-51f52c6d308f>

#lemma(supplement: cite_link(<rijke2025>, "Rijke 2025, prop. 8.2.3"))[
    Let $A$ be a type equipped with a
    #link("note://36f1a370-ca8c-4053-8ee6-d284b50b90e5")[decision] and suppose
    we have a map
    $
        A -> Decision(B).
    $
    Then there are decisions for $A times B$ and $A -> B$.
]

See #link("note://23a01b78-e433-4a66-8915-bfda82ee149a")[Product type].

```agda
decide-×' : {i j : Level} {A : Type i} {B : Type j} →
            Decision A → (A → Decision B) → Decision (A × B)
decide-×' (inject₁ x) g with g x
... | inject₁ y = inject₁ $ pair x y
... | inject₂ h = inject₂ $ h ∘ project₂
decide-×' (inject₂ f) g = inject₂ $ f ∘ project₁

decide-→' : {i j : Level} {A : Type i} {B : Type j} →
            Decision A → (A → Decision B) → Decision (A → B)
decide-→' (inject₁ x) g with g x
... | inject₁ y = inject₁ $ constant y 
... | inject₂ h = inject₂ $ λ k → h (k x)
decide-→' (inject₂ f) g = inject₁ $ Empty.recursion ∘ f
```

= Boolean reflection of a decision <note:356a49b5-ad65-4212-a743-b31b8cdfa8a4>
 
Let $A$ be a type. We define a
#link("note://b05d0e2e-b6ab-45ab-9277-9559f4ee5e1f")[family of types]
$
    sans("Reflects") ofType Decision(A) -> Bool -> cal(U)_0
$
by case analysis
$
    sans("Reflects")(inject1(x), btrue) & = unitType, \
    sans("Reflects")(inject2(f), bfalse) & = unitType, \
    sans("Reflects")(\_, \_) & = emptyType.
$
An inhabitant of $sans("Reflects")(d, b)$ witnesses that the boolean $b$
correctly "reflects" the decision $d$.


```agda
Reflects : {i : Level} {A : Type i} →
          Decision A → 𝟐 → Type zero
Reflects (inject₁ x) false = 𝟎
Reflects (inject₁ x) true = 𝟏
Reflects (inject₂ f) false = 𝟏
Reflects (inject₂ f) true = 𝟎
```

= Boolean reflection principle <note:ce0520ff-51cc-4901-ad90-e0dd4f57237f>

#theorem(supplement: [Boolean reflection principle; #cite_link(<rijke2025>, "Rijke 2025, thm. 8.6.2")])[
    Let $A$ be a type. For all
    #link("note://36f1a370-ca8c-4053-8ee6-d284b50b90e5")[decisions] $d ofType
    Decision(A)$ and
    #link("note://78e3004d-88e7-45e5-8d4d-da76962195f3")[booleans] $b ofType
    Bool$, there is a map
    $
        sans("Reflects")(d, b) -> "if" med b med "then" med A med "else" med not A.
    $
]

See #link("note://356a49b5-ad65-4212-a743-b31b8cdfa8a4")[Boolean reflection of a decision].
 
```agda
reflect : {i : Level} {A : Type i} →
          (d : Decision A) (b : 𝟐) → Reflects d b → if b then A else (¬ A)
reflect (inject₁ x) true ⋆ = x
reflect (inject₂ f) false ⋆ = f

reflectTrue : {i : Level} {A : Type i} →
              (d : Decision A) → Reflects d true → A
reflectTrue (inject₁ x) ⋆ = x

reflectFalse : {i : Level} {A : Type i} →
               (d : Decision A) → Reflects d false → ¬ A
reflectFalse (inject₂ f) ⋆ = f
```
