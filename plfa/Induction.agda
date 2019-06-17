module plfa.Induction where

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong; sym)
open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; _≡⟨_⟩_; _∎)
open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _∸_)
open import Data.Nat.Base using (_^_)
open import Function

-- Exercise operators
-- Logical AND and OR have
-- an identity: true for AND, false for OR;
-- are commutative and associative;
-- distribute over each other (both ways!)

-- Subtraction, or monus (∸), has an identity (zero),
-- is associative, but is not commutative.

_ : (3 + 4) + 5 ≡ 3 + (4 + 5)
_ =
  begin
    (3 + 4) + 5
  ≡⟨⟩
    7 + 5
  ≡⟨⟩
    12
  ≡⟨⟩
    3 + 9
  ≡⟨⟩
    3 + (4 + 5)
  ∎

+-assoc : ∀ (m n p : ℕ) → (m + n) + p ≡ m + (n + p)
+-assoc zero n p =
  begin
    (zero + n) + p
  ≡⟨⟩
    n + p
  ≡⟨⟩
    zero + (n + p)
  ∎
+-assoc (suc m) n p =
  begin
    (suc m + n) + p
  ≡⟨⟩
    suc (m + n) + p
  ≡⟨⟩
    suc ((m + n) + p)
  ≡⟨ cong suc (+-assoc m n p) ⟩
    suc (m + (n + p))
  ≡⟨⟩
    suc m + (n + p)
  ∎

+-identityʳ : ∀ (m : ℕ) → m + zero ≡ m
+-identityʳ zero =
  begin
    zero + zero
  ≡⟨⟩
    zero
  ∎
+-identityʳ (suc m) =
  begin
    suc m + zero
  ≡⟨⟩
    suc (m + zero)
  ≡⟨ cong suc (+-identityʳ m) ⟩
    suc m
  ∎

+-suc : ∀ (m n : ℕ) → m + suc n ≡ suc (m + n)
+-suc zero n =
  begin
    zero + suc n
  ≡⟨⟩
    suc n
  ≡⟨⟩
    suc (zero + n)
  ∎
+-suc (suc m) n =
  begin
    suc m + suc n
  ≡⟨⟩
    suc (m + suc n)
  ≡⟨ cong suc (+-suc m n) ⟩
    suc (suc (m + n))
  ≡⟨⟩
    suc (suc m + n)
  ∎

+-comm : ∀ (m n : ℕ) → m + n ≡ n + m
+-comm m zero =
  begin
    m + zero
  ≡⟨ +-identityʳ m ⟩
    m
  ≡⟨⟩
    zero + m
  ∎
+-comm m (suc n) =
  begin
    m + suc n
  ≡⟨ +-suc m n ⟩
    suc (m + n)
  ≡⟨ cong suc (+-comm m n) ⟩
    suc (n + m)
  ≡⟨⟩
    suc n + m
  ∎

+-rearrange : ∀ (m n p q : ℕ) → (m + n) + (p + q) ≡ m + (n + p) + q
+-rearrange m n p q =
  begin
    (m + n) + (p + q)
  ≡⟨ sym (+-assoc (m + n) p q) ⟩
    ((m + n) + p) + q
  ≡⟨ cong (_+ q) (+-assoc m n p) ⟩
    m + (n + p) + q
  ∎

-- Exercise finite-+-assoc
-- Day 0

-- Day 1
-- 0 : ℕ

-- Day 2
-- 1 : ℕ
-- (0 + 0) + 0 ≡ 0 + (0 + 0)

-- Day 3
-- 2 : ℕ
-- (0 + 0) + 1 ≡ 0 + (0 + 1)
-- (0 + 1) + 0 ≡ 0 + (1 + 0)
-- (0 + 1) + 1 ≡ 0 + (1 + 1)
-- (1 + 0) + 0 ≡ 1 + (0 + 0)
-- (1 + 0) + 1 ≡ 1 + (0 + 1)
-- (1 + 1) + 0 ≡ 1 + (1 + 0)
-- (1 + 1) + 1 ≡ 1 + (1 + 1)

-- Day 4
-- 3 : ℕ
-- (0 + 0) + 2 ≡ 0 + (0 + 2)
-- (0 + 1) + 2 ≡ 0 + (1 + 2)
-- (0 + 2) + 0 ≡ 0 + (2 + 0)
-- (0 + 2) + 1 ≡ 0 + (2 + 1)
-- (0 + 2) + 2 ≡ 0 + (2 + 2)
-- (1 + 0) + 2 ≡ 1 + (0 + 2)
-- (1 + 1) + 2 ≡ 1 + (1 + 2)
-- (1 + 2) + 0 ≡ 1 + (2 + 0)
-- (1 + 2) + 1 ≡ 1 + (2 + 1)
-- (1 + 2) + 2 ≡ 1 + (2 + 2)
-- (2 + 0) + 0 ≡ 2 + (0 + 0)
-- (2 + 0) + 1 ≡ 2 + (0 + 1)
-- (2 + 0) + 2 ≡ 2 + (0 + 2)
-- (2 + 1) + 0 ≡ 2 + (1 + 0)
-- (2 + 1) + 1 ≡ 2 + (1 + 1)
-- (2 + 1) + 2 ≡ 2 + (1 + 2)
-- (2 + 2) + 0 ≡ 2 + (2 + 0)
-- (2 + 2) + 1 ≡ 2 + (2 + 1)
-- (2 + 2) + 2 ≡ 2 + (2 + 2)

+-assoc′ : ∀ (m n p : ℕ) → (m + n) + p ≡ m + (n + p)
+-assoc′ zero n p = refl
+-assoc′ (suc m) n p rewrite +-assoc′ m n p = refl

+-identity′ : ∀ (n : ℕ) → n + zero ≡ n
+-identity′ zero = refl
+-identity′ (suc n) rewrite +-identity′ n = refl

+-suc′ : ∀ (m n : ℕ) → m + suc n ≡ suc (m + n)
+-suc′ zero n = refl
+-suc′ (suc m) n rewrite +-suc′ m n = refl

+-comm′ : ∀ (m n : ℕ) → m + n ≡ n + m
+-comm′ m zero rewrite +-identity′ m = refl
+-comm′ m (suc n) rewrite +-suc′ m n | +-comm′ m n = refl

-- Exercises
+-swap : (m n p : ℕ) → m + (n + p) ≡ n + (m + p)
+-swap m n p =
  begin
    m + (n + p)
  ≡⟨ sym (+-assoc m n p) ⟩
    (m + n) + p
  ≡⟨ cong (_+ p) (+-comm m n) ⟩
    (n + m) + p
  ≡⟨ +-assoc n m p ⟩
    n + (m + p)
  ∎

*-distrib-+ : (m n p : ℕ) → (m + n) * p ≡ m * p + n * p
*-distrib-+ zero n p = refl
*-distrib-+ (suc m) n p rewrite *-distrib-+ m n p =
  sym (+-assoc p (m * p) (n * p))

*-assoc : (m n p : ℕ) → (m * n) * p ≡ m * (n * p)
*-assoc zero n p = refl
*-assoc (suc m) n p rewrite *-distrib-+ n (m * n) p | *-assoc m n p = refl

n*0≡0 : (n : ℕ) → n * 0 ≡ 0
n*0≡0 zero = refl
n*0≡0 (suc n) = n*0≡0 n

n+[m+k]≡m+[n+k] : (n m k : ℕ) → n + (m + k) ≡ m + (n + k)
n+[m+k]≡m+[n+k] n m k =
  begin
    n + (m + k)
  ≡⟨ sym (+-assoc n m k) ⟩
    (n + m) + k
  ≡⟨ cong (flip _+_ k) (+-comm n m) ⟩
    (m + n) + k
  ≡⟨ +-assoc m n k ⟩
    m + (n + k)
  ∎

n+n*m≡n*[1+m] : (n m : ℕ) → n + n * m ≡ n * suc m
n+n*m≡n*[1+m] zero m =
  begin
    0 + 0 * m
  ≡⟨⟩
    0
  ≡⟨⟩
    0 * suc m
  ∎
n+n*m≡n*[1+m] (suc n) m =
  begin
    suc n + suc n * m
  ≡⟨⟩
    suc (n + suc n * m)
  ≡⟨⟩
    suc (n + (m + n * m))
  ≡⟨ cong suc (n+[m+k]≡m+[n+k] n m (n * m)) ⟩
    suc (m + (n + n * m))
  ≡⟨ cong (suc ∘ _+_ m) (n+n*m≡n*[1+m] n m) ⟩
    suc (m + n * suc m)
  ≡⟨⟩
    suc m + n * suc m
  ≡⟨⟩
    suc n * suc m
  ∎

*-comm : (m n : ℕ) → m * n ≡ n * m
*-comm zero n = sym (n*0≡0 n)
*-comm (suc m) n =
  begin
    suc m * n
  ≡⟨⟩
    n + m * n
  ≡⟨ cong (_+_ n) (*-comm m n) ⟩
    n + n * m
  ≡⟨ n+n*m≡n*[1+m] n m ⟩
    n * suc m
  ∎

0∸n≡0 : ∀ n → 0 ∸ n ≡ 0
0∸n≡0 zero = refl
0∸n≡0 (suc n) = refl

∸-+-assoc : ∀ m n p → m ∸ n ∸ p ≡ m ∸ (n + p)
∸-+-assoc zero n p =
  begin
    0 ∸ n ∸ p
  ≡⟨ cong (flip _∸_ p) (0∸n≡0 n) ⟩
    0 ∸ p
  ≡⟨ 0∸n≡0 p ⟩
    0
  ≡⟨ sym (0∸n≡0 (n + p)) ⟩
    0 ∸ (n + p)
  ∎
∸-+-assoc (suc m) zero p = refl
∸-+-assoc (suc m) (suc n) p = ∸-+-assoc m n p

^-distrib-+ : ∀ m n p → m ^ (n + p) ≡ m ^ n * m ^ p
^-distrib-+ m zero p = sym (+-identityʳ (m ^ p))
^-distrib-+ m (suc n) p =
  begin
    m ^ (suc n + p)
  ≡⟨⟩
    m * m ^ (n + p)
  ≡⟨ cong (_*_ m) (^-distrib-+ m n p) ⟩
    m * (m ^ n * m ^ p)
  ≡⟨ sym (*-assoc m (m ^ n) (m ^ p)) ⟩
    m * m ^ n * m ^ p
  ≡⟨⟩
    m ^ (suc n) * m ^ p
  ∎
