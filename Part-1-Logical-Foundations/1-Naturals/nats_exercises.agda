-- 2024/07/28 --

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl)
open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; _∎)

data ℕ : Set where
    zero : ℕ
    suc : ℕ → ℕ

{-# BUILTIN NATURAL ℕ #-}

-- PLUS --
_+_ : ℕ → ℕ → ℕ
zero + n = n
(suc m) + n = suc (m + n)

_ : 2 + 3 ≡ 5
_ =
    begin
      2 + 3
    ≡⟨⟩
      (suc (suc 0)) + (suc (suc (suc 0)))
    ≡⟨⟩
      suc ((suc 0) + (suc (suc (suc 0))))
    ≡⟨⟩
      suc (suc (0 + (suc (suc (suc 0)))))
    ≡⟨⟩
      suc (suc (suc (suc (suc 0))))
    ≡⟨⟩
      5
    ∎

_ : 3 + 4 ≡ 7
_ =
    begin
        3 + 4
    ≡⟨⟩
        suc (2 + 4)
    ≡⟨⟩
        suc (suc (1 + 4))
    ≡⟨⟩
        suc (suc (suc (0 + 4)))
    ≡⟨⟩
        suc (suc (suc 4))
    ≡⟨⟩
        7
    ∎

-- MULT --
_*_ : ℕ → ℕ → ℕ
zero * n = zero
(suc m) * n = n + (m * n)

-- This compact proof style looks cleaner.
_ : 3 * 4 ≡ 12
_ =
    begin
        3 * 4
    ≡⟨⟩ 4 + (2 * 4)
    ≡⟨⟩ 4 + (4 + (1 * 4))
    ≡⟨⟩ 4 + (4 + (4 + (0 * 4)))
    ≡⟨⟩ 4 + (4 + (4 + 0))
    ≡⟨⟩ 12
    ∎

-- EXP --
_^_ : ℕ → ℕ → ℕ
m ^ 0 = 1
m ^ (suc n) = m * (m ^ n)

_ : 3 ^ 4 ≡ 81
_ =
    begin
        3 ^ 4
    ≡⟨⟩ 3 * (3 ^ 3)
    ≡⟨⟩ 3 * (3 * (3 ^ 2))
    ≡⟨⟩ 3 * (3 * (3 * (3 ^ 1)))
    ≡⟨⟩ 3 * (3 * (3 * (3 * (3 ^ 0))))
    ≡⟨⟩ 3 * (3 * (3 * (3 * 1)))
    ≡⟨⟩ 81
    ∎

-- MONUS --
_∸_ : ℕ → ℕ → ℕ
m ∸ zero = m
zero ∸ suc n = zero
suc m ∸ suc n = m ∸ n

_ : 5 ∸ 3 ≡ 2
_ =
    begin
        5 ∸ 3
    ≡⟨⟩ 4 ∸ 2
    ≡⟨⟩ 3 ∸ 1
    ≡⟨⟩ 2 ∸ 0
    ≡⟨⟩ 2
    ∎

_ : 3 ∸ 5 ≡ 0
_ =
    begin
        3 ∸ 5
    ≡⟨⟩ 2 ∸ 4
    ≡⟨⟩ 1 ∸ 3
    ≡⟨⟩ 0 ∸ 2
    ≡⟨⟩ 0
    ∎

infixl 6  _+_  _∸_
infixl 7  _*_

-- GOALS --
_p_ : ℕ → ℕ → ℕ
zero p n = n 
suc m p n = suc (m p n)

-- NATS AS BIN --
data Bin : Set where
    ⟨⟩ : Bin
    _O : Bin → Bin
    _I : Bin → Bin

inc : Bin → Bin
inc ⟨⟩ = ⟨⟩ I
inc (m O) = m I
inc (m I) = (inc m) O

_ : inc (⟨⟩ I) ≡ ⟨⟩ I O
_ = begin
        inc (⟨⟩ I)
    ≡⟨⟩ (inc ⟨⟩) O
    ≡⟨⟩ ⟨⟩ I O
    ∎

_ : inc (⟨⟩ I O I I) ≡ ⟨⟩ I I O O
_ = begin
        inc (⟨⟩ I O I I)
    ≡⟨⟩ (inc (⟨⟩ I O I)) O
    ≡⟨⟩ (inc (⟨⟩ I O) O) O
    ≡⟨⟩ ((⟨⟩ I I) O) O
    ≡⟨⟩ ⟨⟩ I I O O
    ∎

to_ : ℕ → Bin
to 0 = ⟨⟩ O
to (suc m) = inc (to m)

from_ : Bin → ℕ
from ⟨⟩ = 0
from (m O) = 2 * (from m)
from (m I) = (2 * (from m)) + 1

_ : to 14 ≡ ⟨⟩ I I I O
_ = refl

_ : from (⟨⟩ I O I O) ≡ 10
_ = refl
