#import("../../../../../library/template.typ"): *

#show: template

```agda
module Data.Sigma.Definitions where

open import Base.Function.Core
open import Base.Identity.Core hiding (induction)
open import Base.Identity.Definitions
open import Base.Universe
open import Data.Sigma.Core
```

= Currying and uncurring <note:bc0fb217-3c37-4034-9681-ab3040569951>
 
In functional programming, *currying* transforms a function taking multiple
arguments in the form of a
#link("note://ae098784-7572-4d29-b548-a2db9b6d004a")[product] into a sequence of
higher order functions, each of a single argument.

If we have a function $f ofType A times B -> C$, the curried form of this
function would be $f' ofType A -> (B -> C)$, where the application of $f'$ to
each $x ofType A$ yields a new function $f'(x) ofType B -> C$.

We can define a *curry* operator as a higher-order function which takes a
function on #link("note://ae098784-7572-4d29-b548-a2db9b6d004a")[pairs] and
returns its curried form. We allow
#link("note://ae098784-7572-4d29-b548-a2db9b6d004a")[dependent products], not
just ordinary #link("note://23a01b78-e433-4a66-8915-bfda82ee149a")[Cartesian
products] as in the example above.

```agda
curry : {i j k : Level} {A : Type i} {B : A → Type j} {C : Σ A B → Type k} →
        ((u : Σ A B) → C u) →
        ((x : A) → (y : B x) → C $ pair x y)
curry f x y = f $ pair x y
```

We can also define an *uncurry* operator, which takes a curried function and
returns a verion which takes its argument as a pair.

```agda
uncurry : {i j k : Level}
          {A : Type i} {B : A → Type j} {C : (x : A) → B x → Type k} →
          ((x : A) (y : B x) → C x y) →
          ((u : Σ A B) → C (project₁ u) (project₂ u))
uncurry {C = C} = induction {P = λ u → C (project₁ u) (project₂ u)}
```

Compare #cite(<rijke2025>, form: "prose", supplement: "rem. 4.6.3").

= Product swap function <note:ee77073e-2222-4957-9ed3-f8a120d8588d>
 
We define a #link("note://23a01b78-e433-4a66-8915-bfda82ee149a")[product] swap
function $A times B -> B times A$.

```agda
swap : {i j : Level} {A : Type i} {B : Type j} →
       A × B → B × A
swap (pair x y) = pair y x
```

= Sigma associate functions <note:27424231-9e91-44a9-8311-360d17718901>

We define associate functions for
#link("note://ae098784-7572-4d29-b548-a2db9b6d004a")[$Sigma$-types].

```agda
associateˡ : {i j k : Level}
             {A : Type i} {B : A → Type j} {C : (x : A) → B x → Type k} →
             Σ (Σ A B) (uncurry C) → Σ A (λ x → Σ (B x) (C x))
associateˡ (pair (pair x y) z) = pair x (pair y z)

associateʳ : {i j k : Level}
             {A : Type i} {B : A → Type j} {C : (x : A) → B x → Type k} →
             Σ A (λ x → Σ (B x) (C x)) → Σ (Σ A B) (uncurry C)
associateʳ (pair x (pair y z)) = pair (pair x y) z

associateˡ' : {i j k : Level} {A : Type i} {B : Type j} {C : Type k} →
              (A × B) × C → A × (B × C)
associateˡ' (pair (pair x y) z) = pair x (pair y z)

associateʳ' : {i j k : Level} {A : Type i} {B : Type j} {C : Type k} →
              A × (B × C) → (A × B) × C
associateʳ' (pair x (pair y z)) = pair (pair x y) z

associateCurriedˡ : {i j k : Level}
                    {A : Type i} {B : A → Type j} {C : (Σ A B) → Type k} →
                    (Σ (Σ A B) C) → (Σ A (λ x → Σ (B x) (curry C x)))
associateCurriedˡ (pair (pair x y) z) = pair x (pair y z)

associateCurriedʳ : {i j k : Level}
                    {A : Type i} {B : A → Type j} {C : (Σ A B) → Type k} →
                    (Σ A (λ x → Σ (B x) (curry C x))) → (Σ (Σ A B) C)
associateCurriedʳ (pair x (pair y z)) = pair (pair x y) z
```

= Characterization of the identity types of sigma types <note:f7ad6df3-6479-4772-b911-5702cd9e6202>

We follow #cite(<rijke2025>, form: "prose", supplement: "def. 9.3.1") in both
the definition given below and the preceeding motivation.

Consider two #link("note://ae098784-7572-4d29-b548-a2db9b6d004a")[pairs]
$
    (x, y), (x', y') ofType sigmaType(x, A) B(x).
$
We cannot directly compare $y ofType B(x)$ and $y' ofType B(x)$, since they are
of different types. However, if there is a
#link("note://261490cb-2887-4247-9a83-7f674e3c9651")[path] $alpha ofType x =
x'$, then we can #link("note://1229c654-047b-4517-9f4c-df4c03224d02")[transport]
$y ofType B(x)$ along $alpha$ and then compare $tr_(B)(alpha, y) ofType B(x')$
with $y' ofType B(x')$ by considering paths of type
$
    tr_(B)(alpha, y) = y'.
$
Therefore the pairs $(x, y)$ and $(x', y')$ should be identical when there are
individual identifications $alpha ofType x = x'$ and $beta ofType tr_(B)(alpha,
y) = y'$. Consequently, we define the following
#link("note://b05d0e2e-b6ab-45ab-9277-9559f4ee5e1f")[type family] for
characterizing the identity types of
#link("note://ae098784-7572-4d29-b548-a2db9b6d004a")[$Sigma$-types].

```agda
Equal : {i j : Level} {A : Type i} {B : A → Type j} →
        (Σ A B) → (Σ A B) → Type (i ⊔ j)
Equal {B = B} u v =
  Σ (project₁ u ＝ project₁ v)
    (λ α → transport B α (project₂ u) ＝ project₂ v)
```

= Sigma swap base functions <note:2b484b41-4405-42e7-bd4d-e35dbe878770>
 
We define a base swap function on
#link("note://ae098784-7572-4d29-b548-a2db9b6d004a")[$Sigma$-types]. This is
used in #link("note://0e627eaa-64e9-47a5-b5a3-37a4e92ba151")[Lemma 26] to
construct an #link("note://32c2ca55-63ba-411b-9052-676a51fd16a1")[equivalence]
between the two types.

```agda
swapBaseˡ : {i j k : Level} {A : Type i} {B : A → Type j} {C : A → Type k} →
            Σ (Σ A B) (C ∘ project₁) → Σ (Σ A C) (B ∘ project₁)
swapBaseˡ (pair (pair x y) z) = (pair (pair x z) y)

swapBaseʳ : {i j k : Level} {A : Type i} {B : Type j} {C : A → B → Type k} →
            Σ A (λ x → Σ B (λ y → C x y)) → Σ B (λ y → Σ A (λ x → C x y))
swapBaseʳ (pair x (pair y z)) = pair y (pair x z)
```

= Product map <note:ec14d7a6-df57-4319-aa85-1f575cb45244>
 
Given maps $f ofType A -> C$, $g ofType B -> D$, we can define a map on
#link("note://23a01b78-e433-4a66-8915-bfda82ee149a")[products] $f times g ofType
A times B -> C times D$ by
$
    (f times g)((x, y)) = (f(x), g(y))
$
@rijke2025[exer. 9.7(a)].

```agda
map : {i j k l : Level}
      {A : Type i} {B : Type j} {C : Type k} {D : Type l} →
      (A → C) → (B → D) → (A × B → C × D)
map f g (pair x y) = pair (f x) (g y)
```
