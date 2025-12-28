#import("../../../../../../library/template.typ"): *

#show: template

```agda
module Data.Sigma.Properties.Equivalence where

open import Base.Function.Core
open import Base.Function.Definitions
open import Base.Function.Properties.Contractible
open import Base.Function.Properties.Equivalence
open import Base.Function.Properties.Fiber
open import Base.Identity.Core
open import Base.Identity.Definitions
open import Base.Truncation.Definitions
open import Base.Universe.Core
open import Data.Sigma.Core
open import Data.Sigma.Definitions
```

= Product swap is its own inverse <note:3da4b91a-9d29-437d-aecd-794a120d4685>

#lemma(label: "9")[
    The #link("note://23a01b78-e433-4a66-8915-bfda82ee149a")[product]
    #link("note://ee77073e-2222-4957-9ed3-f8a120d8588d")[swap function] is its
    own #link("note://32c2ca55-63ba-411b-9052-676a51fd16a1")[inverse].
]
#proof[
    The #link("note://32c2ca55-63ba-411b-9052-676a51fd16a1")[relevant
    homotopies] hold #link("note://ee77073e-2222-4957-9ed3-f8a120d8588d")[by
    definition].
]

Note that I didn't say
#link("note://47767cc9-0064-45d3-8735-203b3236976d")[involutive]. The situation
is the same as #link("note://2311a766-22a2-4a85-91f2-1f3bc032cfff")[Lemma 7],
where I include a small explanation about this.

```agda
swapInverse :
  {i j : Level} {A : Type i} {B : Type j} →
  Inverse (swap {A = B} {B = A}) (swap {A = A} {B = B})
swapInverse = pair H H
  where
  H : {i j : Level} {A : Type i} {B : Type j} →
      (swap {A = B} {B = A}) ∘ (swap {A = A} {B = B}) ∼ identity
  H (pair x y) = reflexive

swapIsEquivalence :
  {i j : Level} {A : Type i} {B : Type j} →
  IsEquivalence (swap {A = A} {B = B})
swapIsEquivalence = inverse→isEquivalence swap swap swapInverse
```

= Left and right sigma associate functions are inverses <note:52df8c7d-2587-4ddf-bfef-29de5ab739d1>

#lemma(label: "10")[
    The left and right
    #link("note://27424231-9e91-44a9-8311-360d17718901")[sigma associate
    functions] are
    #link("note://32c2ca55-63ba-411b-9052-676a51fd16a1")[inverses].
]
#proof[
    The #link("note://32c2ca55-63ba-411b-9052-676a51fd16a1")[relevant
    homotopies] hold #link("note://27424231-9e91-44a9-8311-360d17718901")[by
    definition].
]

```agda
Σ-associateInverse :
  {i j k : Level} {A : Type i} {B : A → Type j} {C : (x : A) → B x → Type k} →
  Inverse (associateˡ {A = A} {B = B} {C = C})
          (associateʳ {A = A} {B = B} {C = C})
Σ-associateInverse {A = A} {B = B} {C = C} = pair H K
  where
  H : associateʳ ∘ associateˡ ∼ (identity {_} {Σ (Σ A B) (uncurry C)})
  H (pair (pair x y) z) = reflexive

  K : associateˡ ∘ associateʳ ∼ (identity {_} {Σ A (λ x → Σ (B x) (C x))})
  K (pair x (pair y z)) = reflexive

×-associateInverse :
  {i j k : Level} {A : Type i} {B : Type j} {C : Type k} →
  Inverse (associateˡ' {A = A} {B = B} {C = C})
          (associateʳ' {A = A} {B = B} {C = C})
×-associateInverse {A = A} {B = B} {C = C} = pair H K
  where
  H : associateʳ' ∘ associateˡ' ∼ (identity {_} {(A × B) × C})
  H (pair (pair x y) z) = reflexive

  K : associateˡ' ∘ associateʳ' ∼ (identity {_} {A × (B × C)})
  K (pair x (pair y z)) = reflexive

Σ-associateCurriedInverse :
  {i j k : Level}
  {A : Type i} {B : A → Type j} {C : (Σ A B) → Type k} →
  Inverse (associateCurriedˡ {A = A} {B = B} {C = C})
          (associateCurriedʳ {A = A} {B = B} {C = C})
Σ-associateCurriedInverse {A = A} {B = B} {C = C} = pair H K
  where
  H : associateCurriedʳ ∘ associateCurriedˡ ∼ (identity {_} {Σ (Σ A B) C})
  H (pair (pair x y) z) = reflexive

  K : associateCurriedˡ ∘ associateCurriedʳ ∼
      (identity {_} {Σ A (λ x → Σ (B x) (curry C x))})
  K (pair x (pair y z)) = reflexive
```

= Double sigma base swap equivalence on right <note:0e627eaa-64e9-47a5-b5a3-37a4e92ba151>
 
#lemma(supplement: cite_link(<rijke2025>, "Rijke 2025, exer. 9.5(a)"))[
    Let $A$ and $B$ be types, and let $C(x, y)$ be a
    #link("note://b05d0e2e-b6ab-45ab-9277-9559f4ee5e1f")[type family] indexed by
    $x ofType A$ and $y ofType B$. Then there is an
    #link("note://32c2ca55-63ba-411b-9052-676a51fd16a1")[equivalence]
    $
        sigmaType(x, A) sigmaType(y, B) C(x, y) tilde.eq
        sigmaType(y, B) sigmaType(x, A) C(x, y)
    $
]
#proof[
    Use #link("note://ae098784-7572-4d29-b548-a2db9b6d004a")[$Sigma$-recursion]
    to define the natural maps back and forth. The
    #link("note://32c2ca55-63ba-411b-9052-676a51fd16a1")[required homotopies]
    then hold by definition.
]

```agda
swapBaseʳ-inverse :
  {i j k : Level} {A : Type i} {B : Type j} {C : A → B → Type k} →            
  Inverse (swapBaseʳ {A = A} {B = B} {C = C})
          (swapBaseʳ {A = B} {B = A} {C = flip C})
swapBaseʳ-inverse {A = A} {B = B} {C = C} = pair H H
  where
  H : {i j k : Level} {A : Type i} {B : Type j} {C : A → B → Type k} →            
      swapBaseʳ ∘ swapBaseʳ ∼ identity {_} {Σ A (λ x → Σ B (λ y → C x y))}
  H (pair x (pair y z)) = reflexive

swapBaseʳ-≃ : 
  {i j k : Level} {A : Type i} {B : Type j} {C : A → B → Type k} →            
  Σ A (λ x → Σ B (λ y → C x y)) ≃ Σ B (λ y → Σ A (λ x → C x y))
swapBaseʳ-≃ = inverse→≃ swapBaseʳ swapBaseʳ swapBaseʳ-inverse
```

= Double sigma base swap equivalence on left <note:8654b3c4-caef-412d-aef6-3e31dcc2418b>
 
#lemma(supplement: cite_link(<rijke2025>, "Rijke 2025, exer. 9.5(b)"))[
    Let $B$ and $C$ be #link("note://b05d0e2e-b6ab-45ab-9277-9559f4ee5e1f")[type
    families] over a type $A$. There is an
    #link("note://32c2ca55-63ba-411b-9052-676a51fd16a1")[equivalence]
    $
        sigmaType(u, sigmaType(x, A) B(x)) C(project1(u)) tilde.eq
        sigmaType(v, sigmaType(x, A) C(x)) B(project1(v)).
    $
]
#proof[
    Use the #link("note://2b484b41-4405-42e7-bd4d-e35dbe878770")[natural maps
    back and forth]. The
    #link("note://32c2ca55-63ba-411b-9052-676a51fd16a1")[required homotopies]
    then hold by definition.
]

```agda
swapBaseˡ-inverse : 
  {i j k : Level} {A : Type i} {B : A → Type j} {C : A → Type k} →            
  Inverse (swapBaseˡ {A = A} {B = B} {C = C})
          (swapBaseˡ {A = A} {B = C} {C = B})
swapBaseˡ-inverse = pair H H
  where
  H : {i j k : Level} {A : Type i} {B : A → Type j} {C : A → Type k} →            
      swapBaseˡ {B = C} {C = B} ∘ swapBaseˡ ∼
      (identity {_} {Σ (Σ A B) (C ∘ project₁)})
  H (pair (pair x y) z) = reflexive
```

= Fiber over the first projection map is equivalent to fiber of a type family <note:f9a042a9-e79b-4277-8d9b-e440679252d5>
 
#lemma(
    label: "39",
    supplement: cite_link(<rijke2025>, "Rijke 2025, exer. 10.7(a)")
)[
    Let $B$ be a #link("note://b05d0e2e-b6ab-45ab-9277-9559f4ee5e1f")[type
    family] over a type $A$. For each $a ofType A$, there is an
    #link("note://32c2ca55-63ba-411b-9052-676a51fd16a1")[equivalence]
    $
        Fiber_(project1)(a) tilde.eq B(a).
    $
]
#proof[
    The map $lambda ((x, y), p) . tr_(B)(p, y)$ has an
    #link("note://32c2ca55-63ba-411b-9052-676a51fd16a1")[inverse] $lambda y
    . ((a, y), refl_(a))$. The
    #link("note://3cb1b8ca-2a77-4c8a-b726-ed8f10dfd208")[homotpies] witnessing
    this hold by definition.
]

See #link("note://96d1fb9a-fd38-48cc-886f-7643637ac1e7")[Fiber of a function
over a point], #link("note://85839d30-6530-4e54-a8ba-efd1c8709928")[Fiber of a
type family], #link("note://1229c654-047b-4517-9f4c-df4c03224d02")[Transport
along a path], and #link("note://ae098784-7572-4d29-b548-a2db9b6d004a")[Sigma
type].

The note #link("note://4988b637-34d2-472b-98f9-34c544f06e62")[Hint about naming
for fiber of a type family] offers commentary about the connection to
#link("note://85839d30-6530-4e54-a8ba-efd1c8709928")[fibers of a type family].

```agda
fiberProject₁→fiber : {i j : Level} {A : Type i} {B : A → Type j} →
                      (a : A) →
                      Fiber (project₁ {A = A} {B = B}) a → B a
fiberProject₁→fiber {B = B} a (pair (pair x y) p) = transport B p y

fiber→fiberProject₁ : {i j : Level} {A : Type i} {B : A → Type j} →
                      (a : A) →
                      B a → Fiber (project₁ {A = A} {B = B}) a
fiber→fiberProject₁ a y = pair (pair a y) reflexive

fiberProject₁→fiberInverse :
  {i j : Level} {A : Type i} {B : A → Type j} →
  (a : A) →
  Inverse (fiberProject₁→fiber {B = B} a) (fiber→fiberProject₁ a)
fiberProject₁→fiberInverse {B = B} a = pair G H
  where
  G : (fiber→fiberProject₁ a) ∘ (fiberProject₁→fiber a) ∼
      identity {_} {Fiber project₁ a}
  G (pair (pair x y) reflexive) = reflexive

  H : (fiberProject₁→fiber {B = B} a) ∘ (fiber→fiberProject₁ a) ∼
      identity {_} {B a}
  H y = reflexive

fiberProject₁→fiberEquivalence : 
  {i j : Level} {A : Type i} {B : A → Type j} →
  (a : A) →
  IsEquivalence (fiberProject₁→fiber {B = B} a)
fiberProject₁→fiberEquivalence a =
  inverse→isEquivalence (fiberProject₁→fiber a)
                        (fiber→fiberProject₁ a)
                        (fiberProject₁→fiberInverse a)

fiberProject≃fiber :
  {i j : Level} {A : Type i} {B : A → Type j} →
  (a : A) →
  Fiber (project₁ {A = A} {B = B}) a ≃ B a
fiberProject≃fiber a =
  pair (fiberProject₁→fiber a) (fiberProject₁→fiberEquivalence a)
```

= Family of functions is a family of equivalences if and only if the induced map on total spaces is an equivalence <note:1e59ed56-2044-4945-8e7e-c97df7680b26>
 
#theorem(
    label: "45",
    supplement: cite_link(<rijke2025>, "Rijke 2025, thm. 11.1.3")
)[
    Let $f ofType piType(x, A) B(x) -> C(x)$ be a family of maps. The following
    are #link("note://27061ddb-2091-46c1-8752-21db2ab57f44")[logically
    equivalent]:

    1. The family $f$ is a
       #link("note://60d115f9-9bef-47af-916a-1a60ea0b3456")[family of
       equivalences].

    2. The #link("note://6561eded-451d-46bb-8194-c64a0acf904e")[induced map on
       total spaces]
       $
           total(f) ofType sigmaType(x, A) B(x) -> sigmaType(x, A) C(x)
       $
       is an #link("note://32c2ca55-63ba-411b-9052-676a51fd16a1")[equivalence].
]
#proof[
    We reduce the claim to a comparison of
    #link("note://96d1fb9a-fd38-48cc-886f-7643637ac1e7")[fibers]. By
    #link("note://984c33bd-7fb6-4432-a0de-ddc279bddc1c")[Theorem 41], a map is
    an #link("note://32c2ca55-63ba-411b-9052-676a51fd16a1")[equivalence] if and
    only if each of its fibers is
    #link("note://f817901c-750e-4575-a259-d83730424ade")[contractible]. Thus it
    suffices to show that the fiber
    $
        Fiber_(total(f))(v)
    $
    is contractible for each $v ofType sigmaType(x, A) C(x)$ if and only if, for
    each $x ofType A$ and $z ofType C(x)$, the fiber
    $
        Fiber_(f(x))(z)
    $
    is contractible.

    #link("note://7a736198-c62d-4ffa-8dc3-30f145d66dab")[Lemma 44] establishes
    an equivalence between these fibers: for each $v ofType sigmaType(x, A)
    C(x)$, we have
    $
        Fiber_(total(f))(v) tilde.eq Fiber_(f(project1(v)))(project2(v)).
    $

    Since contractibility is preserved under equivalence
    (#link("note://41aea79b-658b-464d-b9c4-0326602aa2db")[Lemma 42]), the fiber
    of $total(f)$ over $v$ is contractible if and only if the corresponding
    fiber of the component map $f(project1(v))$ over $project2(v)$ is contractible.

    Hence $total(f)$ is an equivalence if and only if each map $f(x)$ is an
    equivalence, i.e. if and only if $f$ is a family of equivalences.
]

```agda
familyOfEquivalences↔totalIsEquivalence :
  {i j k : Level} {A : Type i} {B : A → Type j} {C : A → Type k}
  (f : (x : A) → B x → C x) →
  ((x : A) → IsEquivalence (f x)) ↔ IsEquivalence (total f)
familyOfEquivalences↔totalIsEquivalence {_} {_} {_} {A} {B} {C} f =
  swap p ∘↔ (Π↔swap q ∘↔ (r ∘↔ (Π↔swap s)))
  where
  p : IsEquivalence (total f) ↔
      ((v : Σ A C) → IsContractible $ Fiber (total f) v)
  p = isEquivalence↔isContractibleFunction
      
  q : (v : Σ A C) →
      (IsContractible $ Fiber (f $ project₁ v) (project₂ v)) ↔
      (IsContractible $ Fiber (total f) v)
  q v = swap $ isEquivalence→isContractible↔isContractible
    (fromFiberTotal f v) (fromFiberTotalIsEquivalence f v) 
                                                    
  r : ((x : A) (z : C x) → IsContractible $ Fiber (f x) z) ↔
      ((x : Σ A C) → IsContractible $ Fiber (f $ project₁ x) (project₂ x))
  r = pair uncurry curry
                   
  s : (x : A) →
         IsEquivalence (f x) ↔
         ((z : C x) → IsContractible $ Fiber (f x) z)
  s x = isEquivalence↔isContractibleFunction
```

= Equivalence lift to total space <note:ca0042cc-2d24-4664-8baa-c538fb438ec2>
 
#lemma(supplement: cite_link(<rijke2025>, "Rijke 2025, lem. 11.1.4"))[
    Let $f ofType A -> B$ be a map and let $C$ be a
    #link("note://b05d0e2e-b6ab-45ab-9277-9559f4ee5e1f")[type family] over
    $B$. If $f$ is an
    #link("note://32c2ca55-63ba-411b-9052-676a51fd16a1")[equivalence], then the
    map
    $
        sigma_(f)(C) := lambda (x, z) . (f(x), z)
        ofType sigmaType(x, A) C(f(x)) -> sigmaType(y, B) C(y)
    $
    is an equivalence.
]

The proof is pretty similar to the proof of
#link("note://1e59ed56-2044-4945-8e7e-c97df7680b26")[Theorem 45]. For details,
see the formal proof below---I'm too lazy to write it out in prose again right
now.

```agda
isEquivalence→totalMapIsEquivalence :
  {i j k : Level} {A : Type i} {B : Type j} {C : B → Type k}
  {f : A → B} →
  IsEquivalence f → IsEquivalence $ totalMap {C = C} f
isEquivalence→totalMapIsEquivalence {_} {_} {_} {A} {B} {C} {f} =
  r ∘ uncurry' ∘ q ∘ p
  where
  p : IsEquivalence f →
      ((y : B) → IsContractible $ Fiber f y)
  p = isEquivalence→isContractibleFunction

  q : ((y : B) → IsContractible $ Fiber f y) →
      ((y : B) (z : C y) →
        IsContractible $ Fiber (totalMap {C = C} f) (pair y z))
  q r y z =
    isEquivalence→isContractible→isContractible₂
      (fromFiberTotal' f (pair y z))
      (fromFiberTotal'IsEquivalence f (pair y z))
      (r y)

  r : ((v : Σ B C) → IsContractible $ Fiber (totalMap f) v) →
      (IsEquivalence $ totalMap {C = C} f)
  r = isContractibleFunction→isEquivalence
```

= A family of maps over a map is a family of equivalences if and only if the other induced map on total spaces (Africa by Toto) is an equivalence <note:f59a5151-306a-43a4-99ba-1975ec2ba4be>
 
#theorem(
    supplement: cite_link(<rijke2025>, "Rijke 2025, thm. 11.1.6")
)[
    Let $f ofType A -> B$ and let $g ofType piType(x, A) C(x) -> D(f(x))$ be a
    #link("note://dd0ebacd-5d30-4a29-a069-9d12805db0db")[family of maps over]
    $f$. Suppose $f$ is an
    #link("note://32c2ca55-63ba-411b-9052-676a51fd16a1")[equivalence]. Then the
    family of maps $g$ over $f$ is a
    #link("note://60d115f9-9bef-47af-916a-1a60ea0b3456")[family of equivalences]
    if and only if the map $total'_(f)(g)$
    (#link("note://dd0ebacd-5d30-4a29-a069-9d12805db0db")[Africa by Toto]) is an
    equivalence.
]

TODO: Write a paper proof. It is basically an appeal to a commutative diagram
and and application of the
#link("note://eb0e793e-d04a-4145-ad54-152aa50d2aee")[3-for-2 property for
equivalences].

Note: this is a generalization of
#link("note://1e59ed56-2044-4945-8e7e-c97df7680b26")[Theorem 45].

```agda
totalTriangle :
  {i j k l : Level} {A : Type i} {B : Type j} {C : A → Type k} {D : B → Type l}
  (f : A → B) (g : (x : A) → C x → D $ f x) →
  total' f g ∼ (totalMap {C = D} f) ∘ (total g)
totalTriangle f g (pair x z) = reflexive

familyOfEquivalences↔totalIsEquivalence' :
  {i j k l : Level} {A : Type i} {B : Type j} {C : A → Type k} {D : B → Type l}
  (f : A → B) (g : (x : A) → C x → D $ f x) →
  IsEquivalence f →
  ((x : A) → IsEquivalence $ g x) ↔ IsEquivalence (total' {D = D} f g) 
familyOfEquivalences↔totalIsEquivalence' {A = A} {D = D} f g p =
  r ∘↔ q
  where
  q : ((x : A) → IsEquivalence $ g x) ↔
      IsEquivalence (total g)
  q = familyOfEquivalences↔totalIsEquivalence g
                                              
  r : IsEquivalence (total g) ↔ IsEquivalence (total' {D = D} f g)
  r = pair (flip t u) (flip s u)
    where
    s : IsEquivalence (total' {D = D} f g) →
        IsEquivalence (totalMap {C = D} f) →
        IsEquivalence (total g)
    s = isEquivalenceLeft→right→top
          (total' f g)
          (totalMap f)
          (total g)
          (totalTriangle f g)

    t : IsEquivalence (total g) →
        IsEquivalence (totalMap {C = D} f) →
        IsEquivalence (total' {D = D} f g)
    t = isEquivalenceTop→right→left
          (total' f g)
          (totalMap f)
          (total g)
          (totalTriangle f g)

    u : IsEquivalence (totalMap {C = D} f)
    u = isEquivalence→totalMapIsEquivalence p
```

= Curry function has a section <note:89c0b826-88d2-47b9-9c24-5cd1468c03ee>

Note, the section is not
$
    uncurry ofType & (piType(x, A) piType(y, B(x)) C(x, y)) -> \
        & (piType(u, sigmaType(x, A) B(x)) C(project1(u), project2(u)))
$
where $C ofType piType(x, A) B(x) -> cal(U)$, but rather
$
    uncurry' ofType & (piType(x, A) piType(y, B(x)) C((x, y))) -> \
        & (piType(u, sigmaType(x, A) B(x)) C(u))
$
where $C ofType sigmaType(x, A) B(x) -> cal(U)$ which lines up with the type
family $C$ used in the
#link("note://bc0fb217-3c37-4034-9681-ab3040569951")[definition of curry].

Certainly `uncurry'` is also a
#link("note://32c2ca55-63ba-411b-9052-676a51fd16a1")[retraction] for `curry`,
but #link("note://9e47d14d-311a-4046-bf89-207c96c5fa2f")[I'm pretty sure that
proving this requires function extensionality].

#lemma(label: "47")[
    The `uncurry'` operator is a
    #link("note://32c2ca55-63ba-411b-9052-676a51fd16a1")[section] of the `curry`
    operator.
]
#proof[
    Let $f ofType piType(u, sigmaType(x, A) B(x)) C(u)$. Our goal is to
    construct a path
    $
        curry(uncurry'(f)) = f.
    $
    By the definitions of
    #link("note://bc0fb217-3c37-4034-9681-ab3040569951")[`curry` and
    `uncurry'`], the left-hand side evaluates to
    $
        lambda x . lambda y . induction_(Sigma)(f, pair(x, y)).
    $
    By the #link("note://ae098784-7572-4d29-b548-a2db9b6d004a")[computation rule
    for $Sigma$-types], we have $induction_(Sigma)(f, pair(x, y)) dot(eq) f(x,
    y)$, so
    $
        lambda x . lambda y . induction_(Sigma)(f, pair(x, y)) dot(eq)
        lambda x . lambda y . f(x, y)
    $
    Then the $eta$-rule for functions gives
    $
        lambda x . lambda y . f(x, y) dot(eq) f.
    $
    Thus we may take $refl_(f(x))$ for the required path.
]


```agda
curryUncurry'Section :
  {i j k : Level} {A : Type i} {B : A → Type j} {C : Σ A B → Type k} →
  RightInverse (curry {C = C}) (uncurry' {C = C})
curryUncurry'Section f = reflexive

-- curryUncurry'Retraction : 
--   {i j k : Level} {A : Type i} {B : A → Type j} {C : Σ A B → Type k} →
--   LeftInverse (curry {C = C}) (uncurry' {C = C})
-- curryUncurry'Retraction f = {!!}
```
