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
-- Simplifying ((suc m) + n) + p ≡ (suc m) + (n + p) to suc((m + n) + p) ≡ suc (m + (n + p)) and rewriting via inductive hypothesis gives us the same term on both sides.

-- COMMUTATIVITY WITH REWRITE --

+-identity-r′ : ∀ (n : ℕ) → n + 0 ≡ n
+-identity-r′ zero = refl
+-identity-r′ (suc m) rewrite +-identity-r′ m = refl
-- Simplifying (suc m) + 0 ≡ suc m to suc (m + 0) = suc (m) and rewriting via inductive hypothesis gives us the same term on both sides.

+-suc′ : ∀ (m n : ℕ) → m + suc n ≡ suc (m + n)
+-suc′ 0 n = refl
+-suc′ (suc m) n rewrite +-suc′ m n = refl

+-comm′ : ∀ (m n : ℕ) → m + n ≡ n + m
+-comm′ m 0 rewrite +-identity-r′ m = refl
+-comm′ m (suc n) rewrite +-suc′ m n | +-comm′ m n = refl
-- Two rewrites, first using +-suc′ lemma and then inductive hypothesis +-comm′.

-- INTERACTIVE PROVING: ASSOCIATIVITY REVISITED --
+-assoc-i : ∀ (m n p : ℕ) → (m + n) + p ≡ m + (n + p)
+-assoc-i zero n p = refl 
+-assoc-i (suc m) n p rewrite +-assoc-i m n p = refl
-- this was proven interactively, via:
--      1. ?    allows us to create a hole, which leaves us an area to be proven
--      2. C-c C-,  allows us to go into the hole and see the (i) goal and (ii) context/variables
--      3. C-c C-r, allows us to fill a (trivial) hole, in this case with refl
--      4. C-c C-c, allows us to split the hole based on a variable in a context
--      5. If we saw that the inductive hypothesis is required, we used rewrite

-- Ex. 1: +-swap
+-swap : ∀ (m n p : ℕ) → m + (n + p) ≡ n + (m + p)
+-swap m n p =
    begin
        m + (n + p)
    ≡⟨ sym (+-assoc m n p) ⟩ (m + n) + p
    ≡⟨ cong (_+ p) (+-comm m n) ⟩ (n + m) + p -- Tricky! note that we can specify which argument of _+_ we want to use cong on
    ≡⟨ +-assoc n m p ⟩ n + (m + p)
    ∎

-- Ex. 2: *-distrib-+
*-distrib-+ : ∀ (m n p : ℕ) → (m + n) * p ≡ (m * p) + (n * p)
*-distrib-+ zero n p = refl 
*-distrib-+ (suc m) n p rewrite *-distrib-+ m n p | sym (+-assoc p (m * p) (n * p)) = refl
-- Done using the interactive method. Neat!

-- Ex. 3: *-assoc
*-assoc : ∀ (m n p : ℕ) → (m * n) * p ≡ m * (n * p)
*-assoc zero n p = refl 
*-assoc (suc m) n p rewrite *-distrib-+ n (m * n) p | *-assoc m n p = refl

-- Ex. 4: *-comm
*-annihilator-r : ∀ (n : ℕ) → n * 0 ≡ 0
*-annihilator-r zero = refl
*-annihilator-r (suc n) rewrite *-annihilator-r n = refl

*-suc : ∀ (m n : ℕ) → m * (suc n) ≡ m + (m * n)
*-suc zero n = refl
*-suc (suc m) n rewrite *-suc m n | sym (+-assoc′ n m (m * n)) | +-comm′ n m | +-assoc′ m n (m * n) = refl
-- Tricky! note that sym_ requires a space (which allows agda to parse the operand)

*-comm : ∀ (m n : ℕ) → m * n ≡ n * m
*-comm m 0 rewrite *-annihilator-r m = refl  
*-comm m (suc n) rewrite *-suc m n  | *-comm m n = refl

-- Ex. 5: 0 ∸ n ≡ 0
∸-0-is-least : ∀ (n : ℕ) → 0 ∸ n ≡ 0
∸-0-is-least 0 = refl
∸-0-is-least (suc n) = refl
-- The proof didn't use the inductive hypothesis. Indeed, we have two cases:
--  Suppose n = 0. Then 0 ∸ 0 = 0 by definition.
--  Suppose n != 0. Then n = suc m for some m. Then 0 ∸ n = 0 by definition.

-- Ex. 6: ∸-+-assoc
-- ∸-+-assoc-lemma : ∀ (m n p : ℕ) → ((suc m) ∸ n) ∸ p ≡ suc m ∸ (n + p)
-- ∸-+-assoc-lemma m zero p = refl
-- ∸-+-assoc-lemma m (suc n) p = {!   !}
∸-+-assoc : ∀ (m n p : ℕ) → (m ∸ n) ∸ p ≡ m ∸ (n + p)
∸-+-assoc zero n p rewrite ∸-0-is-least n | ∸-0-is-least p | ∸-0-is-least (n + p) = refl 
∸-+-assoc (suc m) zero p = refl 
∸-+-assoc (suc m) (suc n) p rewrite ∸-+-assoc m n p = refl
-- Tricky! Required a double/nested induction.

-- Ex. 7: +*^
-- 2024/07/31