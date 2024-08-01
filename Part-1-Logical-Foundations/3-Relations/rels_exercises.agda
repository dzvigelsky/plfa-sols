-- 2024/07/31 --

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong)
open import Data.Nat using (ℕ; zero; suc; _+_)
open import Data.Nat.Properties using (+-comm; +-identityʳ)

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
≤-trans (s≤s m≤n) (s≤s n≤p) = s≤s (≤-trans m≤n n≤p) -- Step: s≤s m≤n is evidence that suc m ≤ suc n. We want to show that if suc n ≤ suc p, then suc m ≤ suc p. But by the induction hypothesis, we have that m ≤ p. So s≤s (m ≤ p) provides evidence that suc m ≤ suc p.

-- Alternative proof, with explicit parameters
≤-trans′ : ∀ (m n p : ℕ)
    → m ≤ n
    → n ≤ p
    --------
    → m ≤ p

≤-trans′ zero n p (z≤n) _ = z≤n 
≤-trans′ (suc m) (suc n) (suc p) (s≤s m≤n) (s≤s n≤p) = s≤s (≤-trans′ m n p m≤n n≤p)
-- Note: what about (s≤s m≤n) z≤n? In this case we have a contradiction as the first evidence implies n is not 0 and the second implies n is 0.