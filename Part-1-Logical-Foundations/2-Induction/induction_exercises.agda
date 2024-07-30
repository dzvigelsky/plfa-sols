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

+-assoc (suc m) n p = -- inductive case
    begin
        ((suc m) + n) + p
    ≡⟨⟩ suc (m + n) + p
    ≡⟨⟩ suc ((m + n) + p)
    ≡⟨ cong suc (+-assoc m n p) ⟩ suc (m + (n + p))
    ≡⟨⟩ suc m + (n + p)
    ∎

-- INDUCTION AS RECURSION --

+-assoc-2 : ∀ (n p : ℕ) → (2 + n) + p ≡ 2 + (n + p) -- instantiate +-assoc with (m = 2)
+-assoc-2 n p =
    begin
        (2 + n) + p
    ≡⟨⟩ suc (1 + n) + p
    ≡⟨⟩ suc ((1 + n) + p)
    ≡⟨ cong suc (+-assoc-1 n p) ⟩ suc (1 + (n + p))
    ≡⟨⟩ 2 + (n + p)
    ∎
    where
    +-assoc-1 : ∀ (n p : ℕ) → (1 + n) + p ≡ 1 + (n + p)
    +-assoc-1 n p =
        begin
            (1 + n) + p
        ≡⟨⟩ suc (0 + n) + p
        ≡⟨⟩ suc ((0 + n) + p)
        ≡⟨ cong suc (+-assoc-0 n p) ⟩ suc (0 + (n + p))
        ≡⟨⟩ 1 + (n + p)
        ∎
        where
        +-assoc-0 : ∀ (n p : ℕ) → (0 + n) + p ≡ 0 + (n + p)
        +-assoc-0 n p =
            begin
                (0 + n) + p
            ≡⟨⟩ n + p
            ≡⟨⟩ 0 + (n + p)
            ∎

-- COMMUTATITY BY INDUCTION --

+-identity-r : ∀ (m : ℕ) → m + 0 ≡ m -- LEMMA 1: 0 is a right identity
+-identity-r zero =
    begin
        0 + 0
    ≡⟨⟩ 0
    ∎
+-identity-r (suc m) =
    begin
        (suc m) + 0
    ≡⟨⟩ suc (m + 0)
    ≡⟨ cong suc (+-identity-r m) ⟩ suc m
    ∎

+-suc : ∀ (m n : ℕ) → m + suc n ≡ suc (m + n) -- LEMMA 2: move suc from second argument out
+-suc 0 n =
    begin
        0 + suc n
    ≡⟨⟩ suc n
    ≡⟨⟩ suc (0 + n)
    ∎
    
+-suc (suc m) n =
    begin
        (suc m) + (suc n)
    ≡⟨⟩ suc (m + suc n)
    ≡⟨ cong suc (+-suc m n) ⟩ suc (suc (m + n))
    ≡⟨⟩ suc (suc m + n)
    ∎

+-comm : ∀ (m n : ℕ) → m + n ≡ n + m -- THEOREM: commutativity of +
+-comm m zero =
    begin
        m + 0
    ≡⟨ +-identity-r m ⟩ m
    ≡⟨⟩ 0 + m
    ∎

+-comm m (suc n) =
    begin
        m + (suc n)
    ≡⟨ +-suc m n ⟩ suc (m + n)
    ≡⟨ cong suc (+-comm m n) ⟩ suc (n + m)
    ≡⟨⟩ (suc n) + m
    ∎

-- REARRANGING --
+-rearrange : ∀ (m n p q : ℕ) → (m + n) + (p + q) ≡ m + (n + p) + q
+-rearrange m n p q =
    begin
        (m + n) + (p + q)
    ≡⟨ +-assoc m n (p + q) ⟩ m + (n + (p + q))
    ≡⟨ cong (m +_) (sym (+-assoc n p q)) ⟩ m + ((n + p) + q)
    ≡⟨ sym (+-assoc m (n + p) q) ⟩ (m + (n + p)) + q
    ≡⟨⟩ m + (n + p) + q
    ∎

-- FINITE + ASSOCIATIVITY CREATION STORY --
-- (Note)   +-assoc : ∀ (m n p : ℕ) → (m + n) + p ≡ m + (n + p)

-- 0: In the beginning, we know nothing...
-- 1: On the first day, we know 0.
--      0 : ℕ
-- 2: On the second day, we know 1 and applications of associativity on 0 with sum 0.
--      0 : ℕ
--      1 : ℕ   (0 + 0) + 0 = 0 + (0 + 0)
-- 3: On the third day, we know 2 and applications of associativity on 0, 1 with sum 1.
--      0 : ℕ
--      1 : ℕ   (0 + 0) + 0 ≡ 0 + (0 + 0)
--      2 : ℕ   (1 + 0) + 0 ≡ 1 + (0 + 0)   (0 + 1) + 0 ≡ 0 + (1 + 0)   (0 + 0) + 1 ≡ 0 + (0 + 1)
-- 4: On the fourth day, we know 3 and applications of associativity on 0, 1, 2 with sum 2.
--      0 : ℕ
--      1 : ℕ   (0 + 0) + 0 ≡ 0 + (0 + 0)
--      2 : ℕ   (1 + 0) + 0 ≡ 1 + (0 + 0)   (0 + 1) + 0 ≡ 0 + (1 + 0)   (0 + 0) + 1 ≡ 0 + (0 + 1)
--      3 : ℕ   (2 + 0) + 0 ≡ 2 + (0 + 0)   (0 + 2) + 0 ≡ 0 + (2 + 0)   (0 + 0) + 2 ≡ 0 + (0 + 2)   (0 + 1) + 1 ≡ 0 + (1 + 1)   (1 + 1) + 0 ≡ 1 + (1 + 0)   (1 + 0) + 1 ≡ 1 + (0 + 1)

-- ASSOCIATIVITY WITH REWRITE --

+-assoc′ : ∀ (m n p : ℕ) → (m + n) + p ≡ m + (n + p)
+-assoc′ zero n p = refl    -- term is equal to itself is 'refl'
+-assoc′ (suc m) n p rewrite +-assoc′ m n p = refl
-- simplifying ((suc m) + n) + p ≡ (suc m) + (n + p) to suc((m + n) + p) ≡ suc (m + (n + p)) and rewriting via inductive hypothesis gives us the same term on both sides.

-- COMMUTATIVITY WITH REWRITE --