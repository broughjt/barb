#import("../../../../../../library/template.typ"): *

#show: template

```agda
{-# OPTIONS -WnoUnsupportedIndexedMatch #-}

module Data.Sigma.Properties.Map where

open import Base.Function.Core
open import Base.Function.Definitions as Function hiding (_⁻¹; _∙_)
open import Base.Function.Properties.Contractible
open import Base.Function.Properties.Equivalence
open import Base.Identity.Core
open import Base.Identity.Definitions
open import Base.Truncation.Definitions
open import Base.Universe.Core
open import Data.Sigma.Core
open import Data.Sigma.Definitions
open import Data.Sigma.Properties.Equivalence
open import Data.Sigma.Properties.Identity
open import Data.Sigma.Properties.Truncation
```

= Product map respects identity and composition <note:f141cf03-b7e0-4bfe-968a-93ec55ac361c>
 
#lemma(
    supplement: cite_link(<rijke2025>, "Rijke 2025, exer. 9.7(b-c)")
)[
    Given $f ofType A -> C$ and $g ofType B -> D$, let
    $
        f times g ofType A + B -> C + D
    $
    denote the #link("note://ec14d7a6-df57-4319-aa85-1f575cb45244")[map
    operation on products]. Then

    1. For all types $A$ and $B$, there is a
       #link("note://3cb1b8ca-2a77-4c8a-b726-ed8f10dfd208")[homotopy]
       $
           id_(A) + id_(B) ~ id_(A + B)
       $
       (see #link("note://efea6413-096d-4249-8ef0-a4de74fcee13")[Identity
       function]).
    2. Given #link("note://bc9568f6-830b-4b4e-9aab-1808b1127cb0")[composable]
       functions
       $
           A -->^f & A' -->^f' & A'', \
           B -->^g & B' -->^g' & B''
       $
       there is a homotopy
       $
           (f' compose f) + (g' compose g) ~ (f' + g') compose (f + g).
       $
]
#proof[
    The homotopies for both statements hold
    #link("note://95fefab8-ba33-4759-8a33-03997164ebab")[by definition].
]

```agda
mapIdentity : {i j : Level} {A : Type i} {B : Type j} →
                 map {A = A} {B = B} identity identity ∼ identity
mapIdentity (pair x y) = reflexive

mapCompose :
  {i j k l m n : Level}
  {A : Type i} {A' : Type j} {A'' : Type k}
  {B : Type l} {B' : Type m} {B'' : Type n}
  (f : A → A') (f' : A' → A'') (g : B → B') (g' : B' → B'') →
  map (f' ∘ f) (g' ∘ g) ∼ (map f' g') ∘ (map f g)
mapCompose f f' g g' (pair x y) = reflexive
```

= Product map respects homotopy <note:f7406835-d23b-438d-a76b-d45d73d3675d>
 
#lemma(
    supplement: cite_link(<rijke2025>, "Rijke 2025, exer. 9.7(d)")
)[
    Given $f ofType A -> C$ and $g ofType B -> D$, let
    $
        f times g ofType A times B -> C times D
    $
    denote the #link("note://ec14d7a6-df57-4319-aa85-1f575cb45244")[map
    operation on products]. If there are
    #link("note://3cb1b8ca-2a77-4c8a-b726-ed8f10dfd208")[homotopies] $H ofType f
    ~ f'$ and $K ofType g ~ g'$, then there is a homotopy $(f times g) ~ (f'
    times g')$.
]
#proof[
    Suppose we are given
    #link("note://3cb1b8ca-2a77-4c8a-b726-ed8f10dfd208")[homotopies] $H ofType f
    ~ f'$ and $K ofType g ~ g'$. We construct a homotopy $(f times g) ~ (f'
    times g')$.

    Fix $(x, y) ofType A times B$. By definition of the
    #link("note://ec14d7a6-df57-4319-aa85-1f575cb45244")[product map operation],
    we need to construct a
    #link("note://261490cb-2887-4247-9a83-7f674e3c9651")[path]
    $
        (f(x), g(y)) = (f'(x), g'(y)).
    $
    Applying the homotopies $H$ and $K$ yields paths
    $
        f(x) = f'(x) quad "and" quad g(y) = g'(y).
    $
    By the #link("note://dbc89e73-b38a-49b8-b20e-06a10e62393b")[characterization
    of the identity types of products], there determine a path
    $
        (f(x), g(y)) = (f'(x), g'(y)).
    $
]

```agda
mapHomotopy : {i j k l : Level}
              {A : Type i} {B : Type j} {C : Type k} {D : Type l}
              {f f' : A → C} {g g' : B → D} →
              f ∼ f' → g ∼ g' → map f g ∼ map f' g'
mapHomotopy H K (pair x y) = Equal-×→＝ $ pair (H x) (K y)
```

= Fibers of the product map are equivalent to a product fibers <note:4b7a647f-a734-4bae-a92b-9bc93ddd003c>

#lemma(label: "58")[
    Let $f ofType A -> C$ and $g ofType B -> D$ be maps, and let $f times g
    ofType A times B -> C times D$ denote the
    #link("note://ec14d7a6-df57-4319-aa85-1f575cb45244")[product map]. For each
    $v ofType C times D$, there is an
    #link("note://32c2ca55-63ba-411b-9052-676a51fd16a1")[equivalence]
    $
        Fiber_(f times g)(v) tilde.eq
        Fiber_(f)(project1(v)) times Fiber_(g)(project2(v)).
    $
]
#proof[
    There are natural maps back and forth for which the
    #link("note://32c2ca55-63ba-411b-9052-676a51fd16a1")[required homotopies]
    hold essentially for free.
]

See #link("note://96d1fb9a-fd38-48cc-886f-7643637ac1e7")[Fiber of a function
over a point].

```agda
fiber-×→×-fiber :
  {i j k l : Level}
  {A : Type i} {B : Type j} {C : Type k} {D : Type l}
  {f : A → C} {g : B → D}
  (v : C × D) →
  Fiber (map f g) v → Fiber f (project₁ v) × Fiber g (project₂ v)
fiber-×→×-fiber {_} {_} {_} {_} {A} {B} {C} {D} {f} {g}
  (pair z w) (pair (pair x y) pq) with ＝→Equal-× pq
... | pair p q = pair (pair x p) (pair y q)

×-fiber→fiber-× :
  {i j k l : Level}
  {A : Type i} {B : Type j} {C : Type k} {D : Type l}
  {f : A → C} {g : B → D}
  (v : C × D) →
  Fiber f (project₁ v) × Fiber g (project₂ v) → Fiber (map f g) v
×-fiber→fiber-× {_} {_} {_} {_} {A} {B} {C} {D} {f} {g}
  (pair z w) (pair (pair x p) (pair y q)) =
  pair (pair x y) (Equal-×→＝ $ pair p q)

fiber-×→×-fiber-inverse :
  {i j k l : Level}
  {A : Type i} {B : Type j} {C : Type k} {D : Type l}
  {f : A → C} {g : B → D}
  (v : C × D) →
  Inverse (fiber-×→×-fiber {f = f} {g = g} v)
          (×-fiber→fiber-× {f = f} {g = g} v)
fiber-×→×-fiber-inverse {_} {_} {_} {_} {A} {B} {C} {D} {f} {g} v@(pair z w) =
  pair G H
  where
  G : (×-fiber→fiber-× v) ∘ (fiber-×→×-fiber v) ∼
      identity {_} {Fiber (map f g) v}
  G (pair (pair x y) reflexive) = reflexive

  H : (fiber-×→×-fiber v) ∘ (×-fiber→fiber-× v) ∼
      identity {_} {Fiber f (project₁ v) × Fiber g (project₂ v)}
  -- TODO: -WnoUnsupportedIndexedMatch
  H (pair (pair x reflexive) (pair y reflexive)) = reflexive

fiber-×→×-fiber-isEquivalence :
  {i j k l : Level}
  {A : Type i} {B : Type j} {C : Type k} {D : Type l}
  {f : A → C} {g : B → D}
  (v : C × D) →
  IsEquivalence (fiber-×→×-fiber {f = f} {g = g} v)
fiber-×→×-fiber-isEquivalence {_} {_} {_} {_} {A} {B} {C} {D} {f} {g} v =
  inverse→isEquivalence (fiber-×→×-fiber v)
                        (×-fiber→fiber-× v)
                        (fiber-×→×-fiber-inverse v)

fiber-×≃×-fiber :
  {i j k l : Level}
  {A : Type i} {B : Type j} {C : Type k} {D : Type l}
  {f : A → C} {g : B → D}
  (v : C × D) →
  Fiber (map f g) v ≃ Fiber f (project₁ v) × Fiber g (project₂ v)
fiber-×≃×-fiber v = pair (fiber-×→×-fiber v) (fiber-×→×-fiber-isEquivalence v)
```

= Product map with composed with swaps is homotopic to swapped product map <note:6bc1a485-68dc-49d2-8178-af527237ecba>
 
#lemma(label: "57")[
    Let $f ofType A -> C$ and $g ofType B -> D$ be maps, and let $f times g
    ofType A times B -> C times D$ denote the
    #link("note://ec14d7a6-df57-4319-aa85-1f575cb45244")[product map]. There is
    a #link("note://3cb1b8ca-2a77-4c8a-b726-ed8f10dfd208")[homotopy]
    $
        g times f ~ swap compose (f times g) compose swap
    $
    (where $swap$ is the
    #link("note://ee77073e-2222-4957-9ed3-f8a120d8588d")[product swap
    function]).
]
#proof[
    Holds by definition pointwise.
]

```agda
map∼swap∘map∘swap :
  {i j k l : Level}
  {A : Type i} {B : Type j} {C : Type k} {D : Type l}
  (f : A → C) (g : B → D) →
  map g f ∼ (swap ∘ map f g ∘ swap)
map∼swap∘map∘swap f g (pair y x) = reflexive
```

= If a product map is an equivalence then so is its swapped version <note:12499b39-90d4-4943-ab0f-e48ee93cac3d>
 
#lemma[
    Let $f ofType A -> C$ and $g ofType B -> D$ be maps. Then
    #link("note://ec14d7a6-df57-4319-aa85-1f575cb45244")[product map] $f times g
    ofType A times B -> C times D$ is an
    #link("note://32c2ca55-63ba-411b-9052-676a51fd16a1")[equivalence] if and
    only if $g times f ofType B times A -> D times C$ is an equivalence.
]
#proof[
    Suppose $f times g$ is an equivalence. The swap map
    $
        swap ofType A times B -> B times A
    $
    is an equivalence by
    #link("note://3da4b91a-9d29-437d-aecd-794a120d4685")[Lemma 9], and the
    #link("note://bc9568f6-830b-4b4e-9aab-1808b1127cb0")[composition] of
    equivalences is an equivalence by
    #link("note://7357b4f8-f609-47f1-8644-046018748ae7")[Lemma 56]. Hence the
    composite map
    $
        swap compose (f times g) compose swap
    $
    is an equivalence.

    By #link("note://6bc1a485-68dc-49d2-8178-af527237ecba")[Lemma 57], there is
    a #link("note://3cb1b8ca-2a77-4c8a-b726-ed8f10dfd208")[homotopy]
    $
        g times f ~ swap compose (f times g) compose swap.
    $
    Since equivalences are invariant under homotopy
    (#link("note://4b08592f-f5db-4f89-a80d-450239d5889c")[Lemma 36]), it follows
    that $g times f$ is an equivalence.

    The converse direction is identical, exchanging the roles of $f$ and $g$.
]

```agda
mapIsEquivalence→swapMapIsEquivalence : 
  {i j k l : Level}
  {A : Type i} {B : Type j} {C : Type k} {D : Type l}
  {f : A → C} {g : B → D} →
  IsEquivalence $ map f g → IsEquivalence $ map g f
mapIsEquivalence→swapMapIsEquivalence {f = f} {g = g} p = s
  where
  q : IsEquivalence $ swap ∘ map f g ∘ swap
  q = isEquivalenceCompose
      (swap ∘ map f g) swap
        (isEquivalenceCompose swap (map f g) swapIsEquivalence p)
        swapIsEquivalence 
          
  r : map g f ∼ (swap ∘ map f g ∘ swap)
  r = map∼swap∘map∘swap f g
                          
  s : IsEquivalence $ map g f
  s = isEquivalence→homotopy→isEquivalence q (r Function.⁻¹ )

mapIsEquivalence↔swapMapIsEquivalence : 
  {i j k l : Level}
  {A : Type i} {B : Type j} {C : Type k} {D : Type l}
  (f : A → C) (g : B → D) →
  (IsEquivalence $ map f g) ↔ (IsEquivalence $ map g f)
mapIsEquivalence↔swapMapIsEquivalence f g =
  pair mapIsEquivalence→swapMapIsEquivalence
       mapIsEquivalence→swapMapIsEquivalence
```

= Product map equivalence if and only if codomain inhabited implies equivalence <note:a9b39966-4aa9-46fc-bef8-147096146abb>
 
#lemma(
    label: "60",
    supplement: cite_link(<rijke2025>, "Rijke 2025, exer. 9.7(e)")
)[
    Let $f ofType A -> C$ and $g ofType B -> D$ be functions. Then the
    #link("note://ec14d7a6-df57-4319-aa85-1f575cb45244")[product map] $f times g
    ofType A times B -> C times D$ is an
    #link("note://32c2ca55-63ba-411b-9052-676a51fd16a1")[equivalence] if and
    only there are maps
    $
        D & -> IsEquivalence(f), \
        C & -> IsEquivalence(g).
    $
]
#proof[
    We reduce the claim to a comparison of
    #link("note://96d1fb9a-fd38-48cc-886f-7643637ac1e7")[fibers]. By
    #link("note://984c33bd-7fb6-4432-a0de-ddc279bddc1c")[Theorem 41], a map is
    an equivalence if and only if each of its fibers is
    #link("note://ce3caacd-6477-4d21-b37e-c5423974464a")[contractible]. Therefore,
    the product map $f times g$ is an equivalence if and only if for every $(z,
    w) ofType C times D$, the fiber
    $
        Fiber_(f times g)((z, w))
    $
    is #link("note://f817901c-750e-4575-a259-d83730424ade")[contractible].

    Fix $z ofType C$ and $w ofType D$. By
    #link("note://4b7a647f-a734-4bae-a92b-9bc93ddd003c")[Lemma 58], there is an
    equivalence
    $
        Fiber_(f times g)((z, w)) tilde.eq Fiber_(f)(z) times Fiber_(g)(w).
    $
    Since equivalences preserve contractibility
    (#link("note://41aea79b-658b-464d-b9c4-0326602aa2db")[Lemma 42]), the fiber
    on the left is contractible if and only if the product on the right is
    contractible. By #link("note://61774716-8c8a-4461-a44f-63d9eb7c0244")[Lemma
    59], a product is contractible if and only if both components are
    contractible. Thus $Fiber_(f times g)((z, w))$ is contractible if and only
    if both $Fiber_(f)(z)$ and $Fiber_(g)(w)$ are contractible.

    Rearranging quantifiers, this shows that $f times g$ is an equivalence if
    and only if for every $w ofType D$, the map $f$ has contractible fibers, and
    for every $z ofType C$, the map $g$ has contractible fibers. By
    #link("note://984c33bd-7fb6-4432-a0de-ddc279bddc1c")[Theorem 41] again, this
    is equivalent to giving maps
    $
        D -> IsEquivalence(f) quad "and" quad C -> IsEquivalence(g)
    $
    as required.
]

The note #link("note://2a4a4ef5-5fd0-4c09-af64-6eda7e15eecd")[Clever use of
fiber characterization of equivalences in Lemma 60] offers a retrospective on
discovering the proof strategy. Initially, I used a much more direct
argument that ended up being really painful. The note describes the insight
that led to the fiber argument.

Intution: It is possible that the product map is vacuously an equivalence
because one of the components of the product in the domain is empty. Asking that
the codomains be inhabited accounts for this fact.

```agda

mapIsEquivalence↔inhabited→isEquivalence :
  {i j k l : Level}
  {A : Type i} {B : Type j} {C : Type k} {D : Type l}
  (f : A → C) (g : B → D) →
  (IsEquivalence $ map f g) ↔
  ((D → IsEquivalence f) × (C → IsEquivalence g))
mapIsEquivalence↔inhabited→isEquivalence {_} {_} {_} {_}
  {A} {B} {C} {D} f g =
  (((s ∘↔ r) ∘↔ (Π↔swap λ x → Π↔swap (q x))) ∘↔ pair curry uncurry') ∘↔ p
  where
  p : (IsEquivalence $ map f g) ↔
      ((v : C × D) → IsContractible $ Fiber (map f g) v)
  p = isEquivalence↔isContractibleFunction

  q : (z : C) (w : D) → 
      (IsContractible $ Fiber (map f g) (pair z w)) ↔
      (IsContractible $ Fiber f z) × (IsContractible $ Fiber g w)
  q z w = ×-contractible ∘↔
          isEquivalence→isContractible↔isContractible
            (fiber-×→×-fiber (pair z w))
            (fiber-×→×-fiber-isEquivalence (pair z w))

  r : ((z : C) (w : D) →
        (IsContractible $ Fiber f z) × (IsContractible $ Fiber g w)) ↔
      ((D → (z : C) → IsContractible $ Fiber f z) ×
       (C → (w : D) → IsContractible $ Fiber g w))
  r = pair r' (uncurry r'')
    where
    r' : ((z : C) (w : D) →
           (IsContractible $ Fiber f z) × (IsContractible $ Fiber g w)) →
         (D → (z : C) → IsContractible $ Fiber f z) ×
         (C → (w : D) → IsContractible $ Fiber g w)
    r' p = pair (λ w z → project₁ $ p z w) (λ z w → project₂ $ p z w)

    r'' : (D → (z : C) → IsContractible $ Fiber f z) →
          (C → (w : D) → IsContractible $ Fiber g w) →
          (z : C) (w : D) →
          (IsContractible $ Fiber f z) × (IsContractible $ Fiber g w)
    r'' p q z w = pair (p w z) (q z w)

  s : ((D → (z : C) → IsContractible $ Fiber f z) ×
       (C → (w : D) → IsContractible $ Fiber g w)) ↔
      ((D → IsEquivalence f) ×
       (C → IsEquivalence g))
  s = pair (map (Π→swap (λ w → isContractibleFunction→isEquivalence))
                (Π→swap (λ z → isContractibleFunction→isEquivalence)))
           (map (Π→swap (λ w → isEquivalence→isContractibleFunction))
                (Π→swap (λ z → isEquivalence→isContractibleFunction)))

mapIsEquivalence→inhabited→isEquivalence :
  {i j k l : Level}
  {A : Type i} {B : Type j} {C : Type k} {D : Type l}
  {f : A → C} {g : B → D} →
  IsEquivalence $ map f g → (D → IsEquivalence f) × (C → IsEquivalence g)
mapIsEquivalence→inhabited→isEquivalence {f = f} {g = g} =
  project₁ $ mapIsEquivalence↔inhabited→isEquivalence f g

mapIsEquivalence→inhabited→isEquivalence₁ :
  {i j k l : Level}
  {A : Type i} {B : Type j} {C : Type k} {D : Type l}
  {f : A → C} {g : B → D} →
  IsEquivalence $ map f g → (D → IsEquivalence f)
mapIsEquivalence→inhabited→isEquivalence₁ =
  project₁ ∘ mapIsEquivalence→inhabited→isEquivalence

mapIsEquivalence→inhabited→isEquivalence₂ :
  {i j k l : Level}
  {A : Type i} {B : Type j} {C : Type k} {D : Type l}
  {f : A → C} {g : B → D} →
  IsEquivalence $ map f g → (C → IsEquivalence g)
mapIsEquivalence→inhabited→isEquivalence₂ =
  project₂ ∘ mapIsEquivalence→inhabited→isEquivalence

inhabited→isEquivalence→mapIsEquivalence : 
  {i j k l : Level}
  {A : Type i} {B : Type j} {C : Type k} {D : Type l}
  {f : A → C} {g : B → D} →
  (D → IsEquivalence f) →
  (C → IsEquivalence g) →
  IsEquivalence $ map f g
inhabited→isEquivalence→mapIsEquivalence {f = f} {g = g} =
  curry $ project₂ $ mapIsEquivalence↔inhabited→isEquivalence f g
```
