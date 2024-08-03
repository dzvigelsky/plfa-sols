-- 2024/07/31 --

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong)
open import Data.Nat using (ℕ; zero; suc; _+_; _*_)
open import Data.Nat.Properties using (+-comm; +-identityʳ; *-comm)

data _≤_ : ℕ → ℕ → Set where
    z≤n : ∀ {n : ℕ} -- z≤n is a constructor name
        --------
        → 0 ≤ n -- 0 ≤ n is a type

    s≤s : ∀ {m n : ℕ}
        → m ≤ n
        --------
        → suc m ≤ suc n -- Takes evidence that m ≤ n holds into evidence that suc m ≤ suc n holds.

_ : 2 ≤ 4
_ = s≤s (s≤s z≤n)
-- 0 ≤ 2 implies 1 ≤ 3, implies 2 ≤ 4.
-- {n : ℕ} means the arguments for z≤n are implicit, guessed at by Agda.

_ : 2 ≤ 4
_ = s≤s {m = 1} {n = 3} (s≤s {0} {2} (z≤n {2}))
-- Can make implcit arguments explicit.

+-identityʳ′ : ∀ {m : ℕ} → m + zero ≡ m
+-identityʳ′ = +-identityʳ _ -- Agda infers an explicit argument from context.

infix 4 _≤_ -- Binds less tightly than _+_ and _*_; Doesn't associate right/left because x ≤ (y ≤ z) and (x ≤ y) ≤ z both don't make sense.

inv-s≤s : ∀ {m n : ℕ} -- Sketches out a rule we can later apply
    → suc m ≤ suc n
    -----------
    → m ≤ n

inv-s≤s (s≤s m≤n) = m≤n -- m≤n is a variable of type m ≤ n; s≤s m≤n has type suc m ≤ suc n.

inv-z≤n : ∀ {m : ℕ}
    → m ≤ 0
    --------
    → m ≡ 0

inv-z≤n (z≤n) = refl

-- Ex. 1: Example of a preorder that is not a partial order. Satisfies:
--      ∀ a . a R a
--      ∀ a, b, c . a R b ∧ b R c → a R c
-- But not:
--      ∀ a, b . a R b ∧ b R a implies a ≡ b
-- i. {(1, 1), (2, 2), (1, 2), (2, 1)}
-- ii. "Is isomophic to"

-- REFLEXIVITY --
≤-refl : ∀ {n : ℕ}
    --------
    → n ≤ n
≤-refl {zero} = z≤n {0} -- base case holds by def-n
≤-refl {suc n} = s≤s ≤-refl -- inductive case holds by applying constructor in def-n to inductive hypothesis

-- TRANSITIVTY --
-- Proof by induction on evidence, rather than on values
≤-trans : ∀ {m n p : ℕ}
    → m ≤ n
    → n ≤ p
    --------
    → m ≤ p

≤-trans (z≤n) _ = z≤n -- Provide evidence that 0 ≤ n; we can omit n ≤ p because we get m ≤ p by 0≤n.
≤-trans (s≤s m≤n) (s≤s n≤p) = s≤s (≤-trans m≤n n≤p) -- Step: s≤s m≤n is evidence that suc m ≤ suc n. So n is of the form (suc n). So our second piece of evidence must be (s≤s n≤p). By the induction hypothesis, we have that m ≤ p. So s≤s (m ≤ p) provides evidence that suc m ≤ suc p, completing our proof where the arguments where refined.

-- Alternative proof, with explicit parameters
≤-trans′ : ∀ (m n p : ℕ)
    → m ≤ n
    → n ≤ p
    --------
    → m ≤ p

≤-trans′ zero n p (z≤n) _ = z≤n 
≤-trans′ (suc m) (suc n) (suc p) (s≤s m≤n) (s≤s n≤p) = s≤s (≤-trans′ m n p m≤n n≤p)
-- Note: what about (s≤s m≤n) z≤n? In this case we have a contradiction as the first evidence implies n is not 0 and the second implies n is 0.

-- 2024/08/01

≤-antisym : ∀ {m n : ℕ}
    → m ≤ n
    → n ≤ m
    --------
    → m ≡ n

≤-antisym z≤n z≤n = refl
≤-antisym (s≤s m≤n) (s≤s n≤m) = cong suc (≤-antisym m≤n n≤m)

-- Ex. 2: Why is it okay to omit cases where one argument is z≤n and the other is s≤s?
-- Suppose we have ≤-antisym z≤n (s≤s m≤n). Then Agda knows (by pattern matching) that m = 0. But then the second witness cannot be s≤s (n≤m), because it implies that m > 0. ≤-antisym (s≤s m≤n) z≤n being invalid follows similarly.

-- TOTALITY --
data Total (m n : ℕ) : Set where -- Data type with parameters
    forward :
        m ≤ n
        --------
        → Total m n
    
    flipped :
        n ≤ m
        --------
        → Total m n

data Total′ : ℕ → ℕ → Set where -- Indexed data type
    forward′ : ∀ {m n : ℕ}
        → m ≤ n
        --------
        → Total′ m n
    
    flipped′ : ∀ {m n : ℕ}
        → n ≤ m
        --------
        → Total′ m n

-- 2024/08/03
≤-total : ∀ (m n : ℕ) → Total m n
≤-total zero n = forward z≤n
≤-total (suc m) 0 = flipped z≤n
≤-total (suc m) (suc n) with ≤-total m n -- ≤-total m n returns a value of type Total m n, we want to match it.
...     | forward m≤n = forward (s≤s m≤n) -- Case 1: Total m n was constructed via forward m≤n. We can get Total (suc m) (suc n) via forward (s≤s m≤n)
...     | flipped n≤m = flipped (s≤s n≤m) -- Case 2: Total m n was constructed via flipped n≤m. Similar to Case 1.

-- Alternative proof via a helper function:
≤-total′ : ∀ (m n : ℕ) → Total m n
≤-total′ 0 n = forward z≤n
≤-total′ (suc m) 0 = flipped z≤n
≤-total′ (suc m) (suc n) = helper (≤-total′ m n)
    where -- With indented definition(s). Variables on LHS of "=" are in scope; as are identifiers on RHS of "="
    helper : Total m n → Total (suc m) (suc n) -- We want to construct Total (suc m) (suc n)
    helper (forward m≤n) = forward (s≤s m≤n) -- Case 1: Total m n constructed via forward.
    helper (flipped n≤m) = flipped (s≤s n≤m) -- Case 2: Total m n constructed via flipped.

-- MONOTONICITY
-- We want to show that + is monotonic w.r.t. ≤. So,
-- ∀ {m n p q : ℕ} → m ≤ n → p ≤ q → m + p ≤ n + q

-- Part 1: Addition is monotonic on the right.
+-monoʳ-≤ : ∀ (n p q : ℕ)
    → p ≤ q
    --------
    → n + p ≤ n + q

+-monoʳ-≤ zero p q p≤q = p≤q
+-monoʳ-≤ (suc n) p q p≤q = s≤s (+-monoʳ-≤ n p q p≤q)

-- Part 2: Addition is monotonic on the left.
+-mono-ˡ≤ : ∀ (n p q : ℕ)
    → n ≤ p
    --------
    → n + q ≤ p + q

+-mono-ˡ≤ n p q n≤p rewrite +-comm n q | +-comm p q = +-monoʳ-≤ q n p n≤p -- Used commutativity of + to reduce proof to Part 1 lemma.

-- Part 3: Th-m.
+-mono-≤ : ∀ (m n p q : ℕ)
    → m ≤ n
    → p ≤ q
    --------
    → m + p ≤ n + q

+-mono-≤ m n p q m≤n p≤q = ≤-trans (+-monoʳ-≤ m p q p≤q) (+-mono-ˡ≤ m n q m≤n) 
-- m + p ≤ m + q and m + q ≤ n + q implies m + p ≤ n + q by transitivity.

--  Ex. 3: *-mono-≤
-- Idea: (m * p ≤ n * p) ∧ (n * p ≤ n * q) ⇒ (m * p ≤ n * q) by transitivity.

*-mono-ˡ-≤ : ∀ (m n p : ℕ)
    → m ≤ n
    --------
    → m * p ≤ n * p

*-mono-ˡ-≤ m n 0 z≤n = z≤n
*-mono-ˡ-≤ (suc m) (suc n) 0 (s≤s x) rewrite *-comm (suc m) 0 = z≤n
*-mono-ˡ-≤ m n (suc p) m≤n rewrite *-comm m (suc p)
    | *-comm n (suc p)
    | *-comm p m
    | *-comm p n
    = +-mono-≤ m n (m * p) (n * p) m≤n (*-mono-ˡ-≤ m n p m≤n)

-- Tricky! We had to use our result about the monotonicity of + w.r.t ≤.

*-mono-ʳ-≤ : ∀ (m n p : ℕ)
    → m ≤ n
    --------
    → p * m ≤ p * n

*-mono-ʳ-≤ m n p m≤n rewrite *-comm p m | *-comm p n = *-mono-ˡ-≤ m n p m≤n

*-mono-≤ : ∀ (m n p q : ℕ)
    → m ≤ n
    → p ≤ q
    --------
    → m * p ≤ n * q

*-mono-≤ m n p q m≤n p≤q = ≤-trans (*-mono-ˡ-≤ m n p m≤n) (*-mono-ʳ-≤ p q n p≤q) -- Similar to +-mono-≤

-- STRICT INEQUALITY

infix 4 _<_

data _<_ : ℕ → ℕ → Set where
    
    z<s : ∀ {n : ℕ}
        --------
        → 0 < suc n

    s<s : ∀ {m n : ℕ}
        → m < n
        --------
        → suc m < suc n

-- Ex. 4: Transitivity of < 
<-trans : ∀ {m n p : ℕ}
    → m < n
    → n < p
    --------
    → m < p

<-trans z<s (s<s n<p) = z<s
<-trans (s<s m<n) (s<s n<p) = s<s (<-trans m<n n<p)

-- Ex. 5: Trichotomy
-- Either m < n, n < m, or m ≡ n.

data Trichotomous (m n : ℕ) : Set where
    
    smaller :
        m < n
        --------
        → Trichotomous m n
    
    bigger :
        n < m -- m > n
        --------
        → Trichotomous m n
    
    equal :
        m ≡ n
        --------
        → Trichotomous m n

<-trichotomous : ∀ (m n : ℕ) → Trichotomous m n

<-trichotomous zero zero = equal refl
<-trichotomous zero (suc n) = smaller z<s
<-trichotomous (suc m) 0 = bigger z<s
<-trichotomous (suc m) (suc n) with <-trichotomous m n
...     | smaller m<n = smaller (s<s m<n)
...     | bigger n<m = bigger (s<s n<m)
...     | equal x=x = equal (cong suc x=x)

-- Ex. 6: +-mono-<
