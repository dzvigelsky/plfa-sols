-- 2024/07/29 --

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong; sym)
open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; _≡⟨_⟩_; _∎)
open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _∸_)

-- ASSOCIATIVITY BY INDUCTION --
+-assoc : ∀ (m n p : ℕ) → (m + n) + p ≡ m + (n + p)

+-assoc zero n p = -- base case
    begin
        (zero + n) + p
    ≡⟨⟩ n + p
    ≡⟨⟩ zero + (n + p)
    ∎

+-assoc (suc m) n p =
    begin
        ((suc m) + n) + p
    ≡⟨⟩ suc (m + n) + p
    ≡⟨⟩ suc ((m + n) + p)
    ≡⟨ cong suc (+-assoc m n p) ⟩ suc (m + (n + p))
    ≡⟨⟩ suc m + (n + p)
    ∎