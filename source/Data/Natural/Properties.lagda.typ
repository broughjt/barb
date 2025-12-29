#import("../../../../../library/template.typ"): *

#show: template

```agda
module Data.Natural.Properties where

open import Algebra.Definitions
open import Base.Family.Definitions
open import Base.Family.Properties
open import Base.Function.Core
open import Base.Function.Definitions hiding (_⁻¹; _∙_)
open import Base.Function.Properties.Equivalence
open import Base.Identity.Core
open import Base.Identity.Definitions
open import Base.Identity.Syntax
open import Base.Truncation.Definitions
open import Base.Truncation.Properties.Contractible
open import Data.Natural.Core
open import Data.Natural.Definitions
open import Data.Sigma.Core
open import Data.Unit.Core
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
+-commutative zero m = (+-unitʳ m) ⁻¹
+-commutative (successor n) m =
  successor (n + m)
    ＝[ pathAction successor (+-commutative n m) ]
  successor (m + n)
    ＝[ +-successor m n ⁻¹ ]
  m + (successor n) ∎
```

= Natural number multiplication is annilhilative <note:ea921516-259a-41f5-8bde-bcead304d8a1>

#lemma(supplement: cite_link(<rijke2025>, "Rijke 2025, exer. 5.5(a)"))[
    #link("note://87e01952-e90c-4a12-96db-6906d98f6755")[Multiplication] by zero
    on #link("note://600e8ce4-83d2-4a92-9295-ccb0aef05689")[natural numbers] is
    annihilative. For any $n ofType NN$, we have
    $
        0 dot.op n = 0 = n dot.op 0.
    $
]
#proof[
    The left identity $0 dot.op n = n$ holds
    #link("note://87e01952-e90c-4a12-96db-6906d98f6755")[by definition].

    For the right identity $n dot.op 0 = 0$, we proceed by induction. The base case
    $
        0 dot.op 0 = 0
    $
    holds #link("note://87e01952-e90c-4a12-96db-6906d98f6755")[by
    definition]. For the inductive step, fix $n ofType NN$ and assume $n dot.op
    0 = 0$. Then
    $
        s(n) dot.op 0 dot(eq) (n dot.op 0) + 0 = n dot.op 0 = 0
    $
    by the #link("note://87e01952-e90c-4a12-96db-6906d98f6755")[definition of
    multiplication], the
    #link("note://551473be-e940-44e8-abf4-0b85434926ef")[right unit law for
    addition], and the inductive hypothesis.
]

```agda
0· : (n : ℕ) → 0 · n ＝ 0
0· n = reflexive

·0 : (n : ℕ) → n · 0 ＝ 0
·0 zero = reflexive
·0 (successor n) =
  (n · 0) + 0
    ＝[ +-unitʳ (n · 0) ]
  (n · 0)
    ＝[ ·0 n ]
  0 ∎
```

= Natural number multiplication satisfies the unit laws <note:29cb87a7-791c-4267-b604-2f59e207b858>
 
#lemma(supplement: cite_link(<rijke2025>, "Rijke 2025, exer. 5.5(a)"))[
    For all $n ofType NN$, we have $1 dot.op n = n = n dot.op 1$.
]
#proof[
    Since
    $
        1 dot.op n dot(eq) s(0) dot.op n dot(eq) (0 dot.op n) + n
        dot(eq) 0 + n dot(eq) n,
    $
    the left identity $1 dot.op n = n$ holds
    #link("note://87e01952-e90c-4a12-96db-6906d98f6755")[by definition].

    For the right identity $n dot.op 1 = n$, we proceed by induction. The base
    case
    $
        0 dot.op 1 = 0
    $

    holds #link("note://87e01952-e90c-4a12-96db-6906d98f6755")[by
    definition]. For the inductive step, fix $n ofType NN$ and assume $n dot.op
    1 = n$. Observe that
    $
        s(n) dot.op 1 & dot(eq) (n dot.op 1) + 1 && "by definition" \
            & = n + 1 && "by the inductive hypothesis" \
            & dot(eq) s(n + 0) && "by the right successor law" \
            & dot(eq) s(n) && "by the right unit law for addition."
    $
    (See the #link("note://ab2f9c2f-4ee1-4846-a907-e2ac1f1dfbe5")[successor
    laws] and the #link("note://551473be-e940-44e8-abf4-0b85434926ef")[unit
    laws] for addition.)
]

```agda
·-unitˡ : (n : ℕ) → 1 · n ＝ n
·-unitˡ n = reflexive

·-unitʳ : (n : ℕ) → n · 1 ＝ n
·-unitʳ zero = reflexive
·-unitʳ (successor n) =
  (n · 1) + 1
    ＝[ pathAction (flip _+_ 1) (·-unitʳ n) ]
  n + 1
    ＝[ +-successor n 0 ]
  successor (n + 0)
    ＝[ pathAction successor (+-unitʳ n) ]
  successor n ∎
```

= Natural number multiplication successor laws <note:9aa65598-8cd7-44a0-92f1-da07d10d1e71>
 
#lemma(supplement: cite_link(<rijke2025>, "Rijke 2025, exer. 5.5(a)"))[
    For all $n, m ofType NN$, we have
    $
        s(n) dot.op m = n dot.op m + m
        quad "and" quad
        n dot.op s(m) = n dot.op m + n.
    $
]
#proof[
    The left identity $s(n) dot.op m = n dot.op m + m$ holds
    #link("note://87e01952-e90c-4a12-96db-6906d98f6755")[by definition].

    For the right identity $n dot.op s(m) = n dot.op m + n$, we proceed by
    induction on $n$. The base case
    $
        0 dot.op s(m) dot(eq) 0 dot(eq) 0 dot.op m + 0
    $

    holds by definition. For the inductive step, fix $n ofType NN$ and assume $n
    dot.op s(m) = n dot.op m + n$. Then we have
    $
        s(n) dot.op s(m) & dot(eq) n dot.op s(m) + s(m) && "by definition" \
            & = (n dot.op m + n) + s(m) && "by the inductive hypothesis" \
            & = s((n dot.op m + n) + m) && "by the right successor addition law" \
            & = s(n dot.op m + (n + m)) && "by associativity of addition" \
            & = s(n dot.op m + (m + n)) && "by commutivity of addition" \
            & = s((n dot.op m + m) + n) && "by associativity of addition" \
            & = (n dot.op m + m) + s(n) && "by the right successor addition law" \
            & dot(eq) s(n) dot.op m + s(n) && "by defintion."
    $
    (See #link("note://ab2f9c2f-4ee1-4846-a907-e2ac1f1dfbe5")[Natural number
    addition successor laws],
    #link("note://34dd370b-4d36-4da0-bcb6-045977183e1f")[Natural number addition
    is associative],
    #link("note://8e89ef5f-82e8-4304-adc0-61f2cd63c6af")[Natural number addition
    is commutative].) This completes the induction.
]

```agda
successor-· : (n m : ℕ) → (successor n) · m ＝ n · m + m
successor-· n m = reflexive

·-successor : (n m : ℕ) → n · (successor m) ＝ n · m + n
·-successor zero m = reflexive
·-successor (successor n) m =
  n · successor m + successor m
    ＝[ pathAction (flip _+_ (successor m)) (·-successor n m) ]
  (n · m + n) + successor m
    ＝[ +-successor _ m ]
  successor ((n · m + n) + m)
    ＝[ pathAction successor (+-associative _ n m) ]
  successor (n · m + (n + m))
    ＝[ pathAction (successor ∘ (_+_ (n · m))) (+-commutative n m) ]
  successor (n · m + (m + n))
    ＝[ pathAction successor (+-associative _ m n ⁻¹) ]
  successor ((n · m + m) + n)
    ＝[ +-successor _ n ⁻¹ ]
  n · m + m + successor n ∎
```

= Natural number multiplication is commutative <note:5371231d-d092-4f5f-be10-f0152aad35d3>

#lemma(supplement: cite_link(<rijke2025>, "Rijke 2025, exer. 5.5(b)"))[
    #link("note://87e01952-e90c-4a12-96db-6906d98f6755")[Multiplication] on the
     #link("note://600e8ce4-83d2-4a92-9295-ccb0aef05689")[natural numbers] is
     #link("note://22261946-d41d-4db3-849d-0511c26b0dea")[commutative].
]
#proof[
    By induction on the left argument. The base case is
    $
        0 dot.op m = m dot.op 0.
    $
    Since $0 dot.op m dot(eq) 0$
    #link("note://87e01952-e90c-4a12-96db-6906d98f6755")[by definition], this
    follows from the #link("note://ea921516-259a-41f5-8bde-bcead304d8a1")[right
    annihilative law for multiplication]. For the inductive step, fix $n ofType
    NN$ and assume $n dot.op m = m dot.op n$. Then
    $
        s(n) dot.op m dot(eq) n dot.op m + m = m dot.op n + m = m dot.op s(n)
    $
    by the inductive hypothesis and the
    #link("note://9aa65598-8cd7-44a0-92f1-da07d10d1e71")[right successor law for
    multiplication].
]

```agda
·-commutative : Commutative _·_
·-commutative zero m = ·0 m ⁻¹
·-commutative (successor n) m =
  n · m + m
    ＝[ pathAction (flip _+_ m) (·-commutative n m) ]
  m · n + m
    ＝[ ·-successor m n ⁻¹ ]
  m · successor n ∎
```

= Natural number multiplication distributes over addition <note:7d6198f6-c435-4fb6-9a7d-e10b48a2c41c>
 
#lemma(supplement: cite_link(<rijke2025>, "Rijke 2025, exer. 5.5(c)"))[
    #link("note://87e01952-e90c-4a12-96db-6906d98f6755")[Multiplication]
    #link("note://950bc0dc-2afc-4bd1-beab-ad2895783cc5")[distributes over]
    #link("note://1be8278b-eb3c-4fc7-8ee4-2e4c9fa92662")[addition] on the
    #link("note://600e8ce4-83d2-4a92-9295-ccb0aef05689")[natural numbers].
]
#proof[
    We prove left distributivity by induction on $n$; right distributivity is
    analogous.

    The base case
    $
        0 dot.op (m + k) = 0 dot.op m + 0 dot.op k
    $
    holds by definition of
    #link("note://87e01952-e90c-4a12-96db-6906d98f6755")[multiplication] and
    #link("note://1be8278b-eb3c-4fc7-8ee4-2e4c9fa92662")[addition]. For the
    inductive step, fix $n ofType NN$ and assume $n dot.op (m + k) = (n dot.op
    m) + (n dot.op k)$. Observe that
    $
        s(n) dot.op (m + k)
            & dot(eq) n dot.op (m + k) + (m + k) && "by definition" \
            & = (n dot.op m + n dot.op k) + (m + k) && "by the inductive hypothesis" \
            & = ((n dot.op m + n dot.op k) + m) + k && "by associativity of addition" \
            & = (n dot.op m + (n dot.op k + m)) + k && "by associativity of addition" \
            & = (n dot.op m + (m + n dot.op k)) + k && "by commutivity of addition" \
            & = ((n dot.op m + m) + n dot.op k) + k && "by associativity of addition" \
            & = (n dot.op m + m) + (n dot.op k + k) && "by associativity of addition" \
            & dot(eq) s(n) dot.op m + s(n) dot.op k && "by definition."
    $
    (See #link("note://8e89ef5f-82e8-4304-adc0-61f2cd63c6af")[Natural number
    addition is commutative] and
    #link("note://34dd370b-4d36-4da0-bcb6-045977183e1f")[Natural number addition
    is associative].)
]

```agda
·-distributesOverˡ-+ : DistributesOverˡ _·_ _+_
·-distributesOverˡ-+ zero m k = reflexive
·-distributesOverˡ-+ (successor n) m k =
  n · (m + k) + (m + k)
    ＝[ pathAction (flip _+_ (m + k)) (·-distributesOverˡ-+ n m k) ]
  (n · m + n · k) + (m + k)
    ＝[ +-associative _ m k ⁻¹ ]
  ((n · m + n · k) + m) + k
    ＝[ pathAction (flip _+_ k) (+-associative (n · m) _ _) ]
  (n · m + (n · k + m)) + k
    ＝[ pathAction (λ ?x → (n · m + ?x) + k) (+-commutative (n · k) m) ]
  (n · m + (m + n · k)) + k
    ＝[ pathAction (flip _+_ k) (+-associative (n · m) _ _ ⁻¹) ]
  ((n · m + m) + n · k) + k
    ＝[ +-associative _ (n · k) k ]
  (n · m + m) + (n · k + k) ∎

·-distributesOverʳ-+ : DistributesOverʳ _·_ _+_
·-distributesOverʳ-+ zero m k = reflexive
·-distributesOverʳ-+ (successor n) m k =
  (n + m) · k + k
    ＝[ pathAction (flip _+_ k) (·-distributesOverʳ-+ n m k) ]
  (n · k + m · k) + k
    ＝[ +-associative (n · k) _ _ ]
  n · k + (m · k + k)
    ＝[ pathAction (_+_ (n · k)) (+-commutative (m · k) k) ]
  n · k + (k + m · k)
    ＝[ +-associative (n · k) _ _ ⁻¹ ]
  (n · k + k) + m · k ∎

·-distributesOver-+ : DistributesOver _·_ _+_
·-distributesOver-+ = pair ·-distributesOverˡ-+ ·-distributesOverʳ-+
```

= Natural number multiplication is associative <note:ee5ab142-f2fd-478b-986f-c2e81d29fa42>
 
#lemma(supplement: cite_link(<rijke2025>, "Rijke 2025, exer. 5.5(d)"))[
    #link("note://87e01952-e90c-4a12-96db-6906d98f6755")[Multiplication] on
    #link("note://600e8ce4-83d2-4a92-9295-ccb0aef05689")[natural numbers] is
    #link("note://9affcc46-5cf0-4627-b909-80ec3cba8a2d")[associative].
]
#proof[
    By induction on the first argument. The base case
    $
        (0 dot.op m) dot.op k = 0 dot.op (m dot.op k)
    $
    holds #link("note://87e01952-e90c-4a12-96db-6906d98f6755")[by
    definition]. For the inductive step, fix $n ofType NN$ and assume $(n dot.op
    m) dot.op k = n dot.op (m dot.op k)$. Then
    $
        (s(n) dot.op m) dot.op k
            & dot(eq) (n dot.op m + m) dot.op k && "by definition" \
            & = (n dot.op m) dot.op k + m dot.op k && "by right-distributivity" \
            & = n dot.op (m dot.op k) + m dot.op k && "by the inductive hypothesis" \
            & dot(eq) s(n) dot.op (m dot.op k) && "by definition," \
    $
    completing the induction. (See
    #link("note://7d6198f6-c435-4fb6-9a7d-e10b48a2c41c")[Natural number
    multiplication distributes over addition].)
]

```agda
·-associative : Associative _·_
·-associative zero m k = reflexive
·-associative (successor n) m k =
  (n · m + m) · k
    ＝[ ·-distributesOverʳ-+ (n · m) m k ]
  (n · m) · k + m · k
    ＝[ pathAction (flip _+_ (m · k)) (·-associative n m k) ]
  n · (m · k) + m · k ∎
```

= Distance zero if and only if eqaul <note:fafe30ff-f03c-459a-a961-cd7d29e6fe66>
 
#lemma(supplement: cite_link(<rijke2025>, "Rijke 2025, exer. 6.5(a)(i)"))[
    For all $n, m ofType NN$, we have $distance(n, m) = 0$ if and only if $n =
    m$.
]
#proof[
    ($==>$) We proceed by induction on both $n$ and $m$.

    If $n dot(eq) 0$ and $m dot(eq) 0$, the conclusion $n = m$ is immediate
    #link("note://261490cb-2887-4247-9a83-7f674e3c9651")[by reflexivity].

    Suppose $n dot(eq) 0$ and $m dot(eq) s(m')$ for some $m' ofType NN$, and
    assume $distance(0, s(m')) =
    0$. #link("note://9dd496bb-370e-481c-81ad-1ace2b8f6a29")[By definition] we
    have have
    $
        distance(0, s(m')) dot(eq) s(m'),
    $
    so the assumption provides a path $s(m') = 0$. Inverting this path yields $0
    = s(m')$, and hence $n = m$. The case $n = s(n')$ and $m dot(eq) 0$ is
    symmetric.
    
    Finally, fix $n, m ofType NN$ and assume as inductive hypothesis that
    $distance(n, m) = 0$ implies $n = m$. If $distance(s(n), s(m)) = 0$, then
    #link("note://9dd496bb-370e-481c-81ad-1ace2b8f6a29")[by definition]
    $
        distance(s(n), s(m)) dot(eq) distance(n, m),
    $
    so the applying the induction hypothesis yields $n = m$. Applying the
    successor function to both sides gives $s(n) = s(m)$ as required.

    ($<==$) We prove the converse by induction on $n$.

    In the base case $n dot(eq) 0$, it suffices by
    #link("note://261490cb-2887-4247-9a83-7f674e3c9651")[path induction] to show
    $distance(0, 0) = 0$, which holds
    #link("note://9dd496bb-370e-481c-81ad-1ace2b8f6a29")[by definition].

    For the inductive step, fix $n ofType NN$ and assume as induction hypothesis
    that $n = m$ implies $distance(n, m) = 0$. Suppose we are given a path $s(n)
    = m$. By path induction, it suffices to consider the case $m = s(n)$ and
    show that $distance(s(n), s(n)) = 0$. Applying the induction hypothesis to
    $refl_(n) ofType n = n$ yields a path
    $
        distance(n, n) = 0.
    $
    #link("note://9dd496bb-370e-481c-81ad-1ace2b8f6a29")[By definition], we have
    $distance(s(n), s(n)) dot(eq) distance(n, n)$, and therefore
    $
        distance(s(n), s(n)) = 0.
    $
    This completes the induction.
]

See #link("note://600e8ce4-83d2-4a92-9295-ccb0aef05689")[Type of natural
numbers] and #link("note://9dd496bb-370e-481c-81ad-1ace2b8f6a29")[Distance
function on natural numbers].

```agda
distance＝0→＝ : {n m : ℕ} → distance n m ＝ 0 → n ＝ m
distance＝0→＝ {zero} {zero} p = reflexive
distance＝0→＝ {zero} {successor m} p = p ⁻¹
distance＝0→＝ {successor n} {zero} p = p
distance＝0→＝ {successor n} {successor m} p =
  pathAction successor (distance＝0→＝ p)

＝→distance＝0 : {n m : ℕ} → n ＝ m → distance n m ＝ 0
＝→distance＝0 {zero} reflexive = reflexive
＝→distance＝0 {successor n} reflexive = ＝→distance＝0 {n} {n} reflexive
```

= Natural number observational equality is reflexive <note:302358e1-2575-413b-9105-0621e0f5444f>
 
#lemma(
    label: "49",
    supplement: cite_link(<rijke2025>, "Rijke 2025, lem. 6.3.2")
)[
    #link("note://4e056c9c-2c11-4992-9838-3dda731d17fa")[Observational equality
    on natural numbers] is
    #link("note://7e7a1c6f-6051-4526-83e9-01d030717ea5")[reflexive].
]
#proof[
    By induction on $n$.

    In the base case $n dot(eq) 0$, unfolding the
    #link("note://4e056c9c-2c11-4992-9838-3dda731d17fa")[definition of
    observational equality] gives
    $
        Equal(0, 0) dot(eq) unitType
    $
    since $distance(0, 0) dot(eq) 0$. Hence $Equal(0, 0)$ is inhabited.

    For the inductive step, fix $n ofType NN$ and assume $Equal(n,
    n)$. #link("note://4e056c9c-2c11-4992-9838-3dda731d17fa")[By definition]
    $
        Equal(s(n), s(n)) dot(eq) Equal(n, n),
    $
    and therefore $Equal(s(n), s(n))$ holds as well.
]

```agda
equalReflexive : Reflexive Equal
equalReflexive zero = ⋆
equalReflexive (successor n) = equalReflexive n
```

= Observational equality on natural numbers characterizes the identity types of natural numbers <note:cc6e8d8b-91c0-4582-8974-97cfb28389a9>

See #link("note://4e056c9c-2c11-4992-9838-3dda731d17fa")[Observational equality
of the natural numbers].
 
#theorem(
    label: "50",
    supplement: cite_link(<rijke2025>, "Rijke 2025, thm. 11.3.1")
)[
    For each $n, m ofType NN$, the
    #link("note://d25ccc40-b51e-466f-b87a-59be3acfa38a")[canonical map]
    $
        n = m -> Equal_(NN)(n, m)
    $
    induced by #link("note://302358e1-2575-413b-9105-0621e0f5444f")[reflexivity]
    is an #link("note://32c2ca55-63ba-411b-9052-676a51fd16a1")[equivalence].
]
#proof[
    By the #link("note://47c2a4df-e0c1-49a6-8ce8-feae75d30105")[fundamental
    theorem of identity types], it is sufficient to show that for each $n ofType
    NN$, the type
    $
        sigmaType(m, NN) Equal_(NN)(n, m)
    $
    is #link("note://f817901c-750e-4575-a259-d83730424ade")[contractible].

    Let $r ofType piType(n, NN) Equal_(NN)(n, n)$ denote the proof of
    #link("note://7e7a1c6f-6051-4526-83e9-01d030717ea5")[reflexivity] for
    #link("note://4e056c9c-2c11-4992-9838-3dda731d17fa")[observational equality]
    given in #link("note://302358e1-2575-413b-9105-0621e0f5444f")[Lemma 49]. For
    each $n ofType NN$, we take $(n, r(n))$ as the
    #link("note://f817901c-750e-4575-a259-d83730424ade")[center of contraction].

    It remains to give the
    #link("note://f817901c-750e-4575-a259-d83730424ade")[contraction] by showing
    that for every $(m, p) ofType sigmaType(m, NN) Equal_(NN)(n, m)$ there is a
    path
    $
        (n, r(n)) = (m, p).
    $
    We proceed by induction on $n$ and $m$.

    - (*Base case*) If both $n$ and $m$ are zero, then $Equal_(NN)(0, 0) dot(eq)
      unitType$ #link("note://4e056c9c-2c11-4992-9838-3dda731d17fa")[by
      definition], and the required path is obtained by reflexivity. The type
      $Equal_(NN)$ is empty if one side is zero and the other is a successor, so
      in these cases the path is obtained via absurdity.
    - (*Inductive step*) Fix $n, m ofType NN$ and let $p ofType Equal_(NN)(s(n),
      s(m))$. #link("note://4e056c9c-2c11-4992-9838-3dda731d17fa")[By
      definition], we have
      $
          Equal_(NN)(s(n), s(m)) dot(eq) Equal_(NN)(n, m).
      $

      Therefore, we can apply the inductive hypothesis to $m$ and $p ofType
      Equal_(NN)(n, m)$ to get a path
      $
          (n, r(n)) = (m, p)
      $
      in $sigmaType(m, NN) Equal_(NN)(n,
      m)$. #link("note://7caf7ee0-9e2a-4761-bee9-25cd52820039")[Applying] the
      successor function to both components yields a path
      $
          (s(n), r(s(n))) = (s(m), p)
      $
      in $sigmaType(m, NN) Equal_(NN)(s(n), m)$ as required.

    Thus $sigmaType(m, NN) Equal_(NN)(n, m)$ is contractible for each $n ofType
    NN$, and hence the canonical map $n = m -> Equal_(NN)(n, m)$ is an
    equivalence.
]

```agda
＝→equal-isEquivalence :
  (n m : ℕ) →
  IsEquivalence (＝→reflexive {R = Equal} equalReflexive {x = n} {y = m})
＝→equal-isEquivalence n =
  totalIsContractible→characterize-＝
    n
    (λ m → ＝→reflexive equalReflexive {x = n} {y = m})
    p
  where
  c : (n : ℕ) → Σ ℕ (Equal n)
  c n = pair n (equalReflexive n)

  C : (n : ℕ) → (u : Σ ℕ (Equal n)) → c n ＝ u
  C zero (pair zero ⋆) = reflexive
  C (successor n) (pair (successor m) p) = pathAction q r
    where
    q : Σ ℕ (Equal n) → Σ ℕ (Equal (successor n))
    q (pair m r) = pair (successor m) r

    r : c n ＝ pair m p
    r = (C n) (pair m p)

  p : IsContractible (Σ ℕ (Equal n))
  p = pair (c n) (C n)

＝≃Equal : (n m : ℕ) → n ＝ m ≃ Equal n m
＝≃Equal n m = pair (＝→reflexive equalReflexive) (＝→equal-isEquivalence n m)

＝↔Equal : (n m : ℕ) → n ＝ m ↔ Equal n m
＝↔Equal n m = ≃→↔ (＝≃Equal n m)

＝→Equal : {n m : ℕ} → n ＝ m → Equal n m
＝→Equal {n} {m} = project₁ $ ＝↔Equal n m

Equal→＝ : {n m : ℕ} → Equal n m → n ＝ m
Equal→＝ {n} {m} = project₂ $ ＝↔Equal n m
```

= Natural number successor function is injective <note:71254972-aba4-48ec-8e9d-df0a9158f268>
 
#theorem(
    supplement: [Peano's seventh axiom; #cite_link(<rijke2025>, "Rijke 2025, thm. 6.4.1")]
)[
    The #link("note://600e8ce4-83d2-4a92-9295-ccb0aef05689")[natural number
    successor function] is
    #link("note://69153807-5e02-4218-8a55-d90ee1a6f5b1")[injective].
]
#proof[
    Let $n, m ofType NN$ and suppose $s(n) = s(m)$. By
    #link("note://cc6e8d8b-91c0-4582-8974-97cfb28389a9")[Theorem 50], identity
    of natural numbers is equivalent to
    #link("note://4e056c9c-2c11-4992-9838-3dda731d17fa")[observational
    equality], so it follows that $Equal(s(n), s(m))$ holds. However, we have
    $
        Equal(s(n), s(m)) dot(eq) Equal(n, m)
    $
    #link("note://4e056c9c-2c11-4992-9838-3dda731d17fa")[by definition], so
    $Equal(n, m)$ holds as well. Applying Theorem 50 again, we conclude that $n
    = m$.

    Thus the successor function is injective.
]

```agda
successorInjective : Injective successor
successorInjective = Equal→＝ ∘ ＝→Equal
```

= The successor of a natural number is never zero <note:efe44f4c-4bbc-4dc5-aa05-32248218ea09>
 
#theorem(
    supplement: [Peano's eighth axiom; #cite_link(<rijke2025>, "Rijke 2025, thm. 6.4.2")]
)[
    For any #link("note://600e8ce4-83d2-4a92-9295-ccb0aef05689")[natural number]
    $n$, we have $s(n) != 0$.
]
#proof[
    Let $n ofType NN$ and suppose $s(n) = 0$. By
    #link("note://cc6e8d8b-91c0-4582-8974-97cfb28389a9")[Theorem 50], this
    implies $Equal(s(n), 0)$. However, the type $Equal(s(n), 0)$ is empty by
    the definition of
    #link("note://4e056c9c-2c11-4992-9838-3dda731d17fa")[observational equality
    on natural numbers], a contradiction.
]

```agda
successor≠0 : (n : ℕ) → successor n ≠ 0
successor≠0 n = ＝→Equal
```
