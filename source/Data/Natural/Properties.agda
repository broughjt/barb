module Data.Natural.Properties where

import Relation.Binary.PropositionalEquality as PropositionalEquality
open PropositionalEquality using (_≡_; reflexive; symmetric; congruent)
open PropositionalEquality.≡-Reasoning
open import Data.Natural.Core

open import Algebra {A = ℕ} _≡_

+-left-identity : LeftIdentity 0 _+_
+-left-identity _ = reflexive

successor-+ : ∀ n m → (successor n) + m ≡ successor (n + m)
successor-+ _ _ = reflexive

+-successor : ∀ n m → n + (successor m) ≡ successor (n + m)
+-successor zero m = reflexive
+-successor (successor n) m = congruent successor (+-successor n m)

+-right-identity : RightIdentity 0 _+_
+-right-identity zero = reflexive
+-right-identity (successor n) = congruent successor (+-right-identity n)

+-associative : Associative _+_
+-associative zero m k = reflexive
+-associative (successor n) m k = congruent successor (+-associative n m k)

+-commutative : Commutative _+_
+-commutative zero m = symmetric (+-right-identity m)
+-commutative (successor n) m =
  begin
    successor n + m
  ≡⟨⟩
    successor (n + m)
  ≡⟨ congruent successor (+-commutative n m) ⟩
    successor (m + n)
  ≡⟨ symmetric (+-successor m n) ⟩
    m + successor n
  ∎
