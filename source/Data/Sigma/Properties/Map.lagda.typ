#import("../../../../../../library/template.typ"): *

#show: template

```agda
module Data.Sigma.Properties.Map where

open import Base.Function.Core
open import Base.Function.Definitions
open import Base.Identity.Core
open import Base.Universe
open import Data.Sigma.Core
open import Data.Sigma.Definitions
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
    TODO
]

```agda
-- mapHomotopy : {i j k l : Level}
--               {A : Type i} {B : Type j} {C : Type k} {D : Type l}
--               {f f' : A → C} {g g' : B → D} →
--               f ∼ f' → g ∼ g' → map f g ∼ map f' g'
-- mapHomotopy H K = {!!}
```
