#import("../../../../../../../library/template.typ"): *

#show: template

```agda
{-# OPTIONS -WnoUnsupportedIndexedMatch #-}

module Scratch.Data.Sigma.Properties.Map where

open import Base.Function.Core
open import Base.Function.Definitions hiding (_⁻¹; _∙_)
open import Base.Function.Properties.Equivalence
open import Base.Identity.Core
open import Base.Identity.Definitions
open import Base.Universe.Core
open import Data.Sigma.Core
open import Data.Sigma.Definitions
open import Data.Sigma.Properties.Identity
```

= Old proof of Lemma 60 <note:59b21db6-d797-4d28-a29a-83c091202e63>

This is an earlier formal proof of part of the statement of
#link("note://a9b39966-4aa9-46fc-bef8-147096146abb")[Lemma 60]. I gave up on
this strategy because I came up with a better one.

```agda
mapIsEquivalence→inhabited→isEquivalence₁ :
  {i j k l : Level}
  {A : Type i} {B : Type j} {C : Type k} {D : Type l}
  {f : A → C} {g : B → D} →
  IsEquivalence $ map f g → (D → IsEquivalence f)
mapIsEquivalence→inhabited→isEquivalence₁
  {_} {_} {_} {_} {A} {B} {C} {D} {f} {g} p w with isEquivalence→hasInverse p
... | pair fg' (pair G H) = inverse→isEquivalence f f' (pair G' H')
  where
  f' : C → A
  f' = project₁ ∘ fg' ∘ flip pair w

  K : (g ∘ project₂) ∼ (project₂ ∘ map f g)
  K (pair x y) = reflexive

  G' : f' ∘ f ∼ identity {_} {A}
  G' x =
    let
      y = project₂ $ fg' $ pair (f x) w

      p : fg' ((map f g) (pair x y)) ＝ pair x y
      p = G $ pair x (project₂ $ fg' $ pair (f x) w)

      p' : (project₁ $ fg' $ pair (f x) (g y)) ＝ x
      p' = project₁ $ ＝→Equal-× p

      q : (map f g) (fg' (pair (f x) w)) ＝ pair (f x) w
      q = H $ pair (f x) w

      r : (g $ project₂ $ fg' $ pair (f x) w) ＝
          (project₂ $ map f g $ fg' $ pair (f x) w)
      r = K $ fg' $ pair (f x) w

      q' : g y ＝ w
      q' = r ∙ (project₂ $ ＝→Equal-× $ q)

      s : (project₁ $ fg' $ pair (f x) (g y)) ＝
          (project₁ $ fg' $ pair (f x) w)
      s = pathAction (λ ?w → project₁ $ fg' $ pair (f x) ?w) q'

      t : f' (f x) ＝ x
      t = s ⁻¹ ∙ p'
    in t

  L : (f ∘ project₁) ∼ (project₁ ∘ map f g)
  L (pair x y) = reflexive

  H' : f ∘ f' ∼ identity {_} {C}
  H' z =
    let
      p : (f $ project₁ $ fg' $ pair z w) ＝
            (project₁ $ map f g $ fg' $ pair z w)
      p = L $ fg' $ pair z w

      q : (project₁ $ map f g $ fg' $ pair z w) ＝ z
      q = project₁ $ ＝→Equal-× $ H $ pair z w
    in p ∙ q
```
