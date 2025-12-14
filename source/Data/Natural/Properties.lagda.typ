#import("../../../../../library/template.typ"): *

#show: template

```agda
module Data.Natural.Properties where

open import Algebra.Definitions
open import Base.Identity.Core
open import Base.Identity.Definitions
open import Base.Identity.Syntax
open import Data.Natural.Core
open import Data.Natural.Definitions
```

= Natural number addition satifies the unit laws <note:551473be-e940-44e8-abf4-0b85434926ef>
 
#lemma(supplement: cite_link(<rijke2025>, "Rijke 2025, prop. 5.6.1"))[
    For all $n ofType NN$, we have $0 + n = n = n + 0$.
]
#proof[
    The left identity $0 + n = n$ holds by
    #link("note://1be8278b-eb3c-4fc7-8ee4-2e4c9fa92662")[definition of
    addition].

    For the right identity, we proceed by induction. The base case is
    $
        0 + 0 = 0
    $
    which holds #link("note://1be8278b-eb3c-4fc7-8ee4-2e4c9fa92662")[by
    definition]. For the inductive step, assume $n + 0 = n$. It follows that
    $
        s(n) + 0 dot(eq) s(n + 0) = s(n),
    $
    since $s(n) + 0 dot(eq) = s(n + 0)$
    #link("note://1be8278b-eb3c-4fc7-8ee4-2e4c9fa92662")[by definition].
]

```agda
+-unitˡ : (n : ℕ) → 0 + n ＝ n
+-unitˡ n = reflexive

+-unitʳ : (n : ℕ) → n + 0 ＝ n
+-unitʳ zero = reflexive
+-unitʳ (successor n) = pathAction successor (+-unitʳ n)
```

= Natural number addition successor laws <note:ab2f9c2f-4ee1-4846-a907-e2ac1f1dfbe5>
 
#lemma(supplement: cite_link(<rijke2025>, "Rijke 2025, prop. 5.6.2"))[
    For all $n, m ofType NN$, we have $s(n) + m = s(n + m) = n + s(m)$.
]
#proof[
    The left identity $s(n) + m = s(n + m)$ holds
    #link("note://1be8278b-eb3c-4fc7-8ee4-2e4c9fa92662")[by definition].

    For the right identity $n + s(m) = s(n + m)$, we proceed by induction on
    $n$. The base case
    $
        0 + s(m) = s(m)
    $
    holds #link("note://1be8278b-eb3c-4fc7-8ee4-2e4c9fa92662")[by
    definition]. For the inductive step, assume $n + s(m) = s(n + m)$. Then
    $
        s(n) + s(m) dot(eq) s(n + s(m)) = s(s(n + m)) dot(eq) s(s(n) + m)
    $
    by #link("note://1be8278b-eb3c-4fc7-8ee4-2e4c9fa92662")[definition of
    addition] and the inductive hypothesis.
]

```agda
successor-+ : (n m : ℕ) → (successor n) + m ＝ successor (n + m)
successor-+ n m = reflexive

+-successor : (n m : ℕ) → n + (successor m) ＝ successor (n + m)
+-successor zero m = reflexive
+-successor (successor n) m = pathAction successor (+-successor n m)
```

= Natural number addition is associative <note:34dd370b-4d36-4da0-bcb6-045977183e1f>
 
#lemma(supplement: cite_link(<rijke2025>, "Rijke 2025, prop. 5.6.3"))[
    #link("note://1be8278b-eb3c-4fc7-8ee4-2e4c9fa92662")[Addition] on
    #link("note://600e8ce4-83d2-4a92-9295-ccb0aef05689")[natural numbers] is
    #link("note://9affcc46-5cf0-4627-b909-80ec3cba8a2d")[associative].
]
#proof[
    Let $n, m, k ofType NN$. We proceed by induction on $n$. We have
    $
        (0 + m) + k dot(eq) m + k dot(eq) 0 + (m + k)
    $
    #link("note://1be8278b-eb3c-4fc7-8ee4-2e4c9fa92662")[by definition], so the
    base case holds. Fix $n$ and assume $(n + m) + k = n + (m + k)$. Then
    $
        (s(n) + m) + k
            & dot(eq) s(n + m) + k && "by definition" \
            & dot(eq) s((n + m) + k) && "by definition" \
            & = s(n + (m + k)) && "by the inductive hypothesis" \
            & dot(eq) s(n) + (m + k) && "by definition" \
    $
    as needed.
]

```agda
+-associative : Associative _+_
+-associative zero m k = reflexive
+-associative (successor n) m k = pathAction successor (+-associative n m k)
```

= Natural number addition is commutative <note:8e89ef5f-82e8-4304-adc0-61f2cd63c6af>
 
#lemma(supplement: cite_link(<rijke2025>, "Rijke 2025, prop. 5.6.4"))[
    #link("note://1be8278b-eb3c-4fc7-8ee4-2e4c9fa92662")[Addition] on the
    #link("note://600e8ce4-83d2-4a92-9295-ccb0aef05689")[natural numbers] is
    #link("note://22261946-d41d-4db3-849d-0511c26b0dea")[commutative].
]
#proof[
    Let $n, m ofType NN$. We proceed by induction on $n$. The base case
    $
        0 + m dot(eq) m = m + 0
    $
    follows by the #link("note://551473be-e940-44e8-abf4-0b85434926ef")[right
    unit law for addition]. Fix $n ofType NN$ and suppose $n + m = m + n$. Then
    $
        s(n) + m
            & dot(eq) s(n + m) && "by definition" \
            & = s(m + n) && "by the inductive hypothesis" \
            & = m + s(n) && "by the right successor law,"
    $
    which completes the induction (see
    #link("note://ab2f9c2f-4ee1-4846-a907-e2ac1f1dfbe5")[Natural number addition
    successor laws]).
]

```agda
+-commutative : Commutative _+_
+-commutative zero m = (+-unitʳ m)⁻¹
+-commutative (successor n) m =
  successor (n + m)
    ＝[ pathAction successor (+-commutative n m) ]
  successor (m + n)
    ＝[ +-successor m n ⁻¹ ]
  m + (successor n) ∎
```
