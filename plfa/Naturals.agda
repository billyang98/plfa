import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl)
open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; _∎)

module plfa.Naturals where

data ℕ : Set where
  zero : ℕ
  suc : ℕ → ℕ

{-# BUILTIN NATURAL ℕ #-}

seven : ℕ
seven = suc (suc (suc (suc (suc (suc (suc zero))))))

_+_ : ℕ → ℕ → ℕ
zero + n = n
suc m + n = suc (m + n)

_ : 2 + 3 ≡ 5
_ =
  begin
    2 + 3
  ≡⟨⟩
    suc (1 + 3)
  ≡⟨⟩
    suc (suc (0 + 3))
  ≡⟨⟩
    suc (suc 3)
  ≡⟨⟩
    5
  ∎

_ : 2 + 3 ≡ 5
_ = refl

+-example : 3 + 4 ≡ 7
+-example =
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

_*_ : ℕ → ℕ → ℕ
zero * n = zero
suc m * n = n + (m * n)

_ =
  begin
    2 * 3
  ≡⟨⟩
    3 + (1 * 3)
  ≡⟨⟩
    3 + (3 + (0 * 3))
  ≡⟨⟩
    3 + (3 + 0)
  ≡⟨⟩
    6
  ∎

*-example : 3 * 4 ≡ 12
*-example =
  begin
    3 * 4
  ≡⟨⟩
    4 + (2 * 4)
  ≡⟨⟩
    4 + (4 + (1 * 4))
  ≡⟨⟩
    4 + (4 + (4 + (0 * 4)))
  ≡⟨⟩
    4 + (4 + (4 + 0))
  ≡⟨⟩
    4 + (4 + 4)
  ≡⟨⟩
    4 + 8
  ≡⟨⟩
    12
  ∎

_^_ : ℕ → ℕ → ℕ
n ^ zero = 1
n ^ suc m = n * (n ^ m)

^-example : 3 ^ 4 ≡ 81
^-example =
  begin
    3 ^ 4
  ≡⟨⟩
    3 * (3 ^ 3)
  ≡⟨⟩
    3 * (3 * (3 ^ 2))
  ≡⟨⟩
    3 * (3 * (3 * (3 ^ 1)))
  ≡⟨⟩
    3 * (3 * (3 * (3 * (3 ^ 0))))
  ≡⟨⟩
    3 * (3 * (3 * (3 * 1)))
  ≡⟨⟩
    3 * (3 * (3 * 3))
  ≡⟨⟩
    3 * (3 * 9)
  ≡⟨⟩
    3 * 27
  ≡⟨⟩
    81
  ∎

_∸_ : ℕ → ℕ → ℕ
m ∸ zero = m
zero ∸ suc n = zero
suc m ∸ suc n = m ∸ n

_ =
  begin
    3 ∸ 2
  ≡⟨⟩
    2 ∸ 1
  ≡⟨⟩
    1 ∸ 0
  ≡⟨⟩
    1
  ∎

_ =
  begin
    2 ∸ 3
  ≡⟨⟩
    1 ∸ 2
  ≡⟨⟩
    0 ∸ 1
  ≡⟨⟩
    0
  ∎

∸-example₁ : 5 ∸ 3 ≡ 2
∸-example₁ =
  begin
    5 ∸ 3
  ≡⟨⟩
    4 ∸ 2
  ≡⟨⟩
    3 ∸ 1
  ≡⟨⟩
    2 ∸ 0
  ≡⟨⟩
    2
  ∎

∸-example₂ : 3 ∸ 5 ≡ 0
∸-example₂ =
  begin
    3 ∸ 5
  ≡⟨⟩
    2 ∸ 4
  ≡⟨⟩
    1 ∸ 3
  ≡⟨⟩
    0 ∸ 2
  ≡⟨⟩
    0
  ∎

infixl 6 _+_ _∸_
infixl 7 _*_

{-# BUILTIN NATPLUS _+_ #-}
{-# BUILTIN NATTIMES _*_ #-}
{-# BUILTIN NATMINUS _∸_ #-}

data Bin : Set where
  nil : Bin
  x0_ : Bin → Bin
  x1_ : Bin → Bin

inc : Bin → Bin
inc nil = x1 nil
inc (x0 x) = x1 x
inc (x1 x) = x0 (inc x)

inc-example₀ : inc (x0 nil) ≡ x1 nil
inc-example₀ = refl

inc-example₁ : inc (x1 nil) ≡ x0 x1 nil
inc-example₁ = refl

inc-example₂ : inc (x0 x1 nil) ≡ x1 x1 nil
inc-example₂ = refl

inc-example₃ : inc (x1 x1 nil) ≡ x0 x0 x1 nil
inc-example₃ = refl

inc-example₄ : inc (x0 x0 x1 nil) ≡ x1 x0 x1 nil
inc-example₄ = refl

to : ℕ → Bin
to zero = x0 nil
to (suc n) = inc (to n)

to-example₀ : to 0 ≡ x0 nil
to-example₀ = refl

to-example₁ : to 1 ≡ x1 nil
to-example₁ = refl

to-example₂ : to 2 ≡ x0 x1 nil
to-example₂ = refl

to-example₃ : to 3 ≡ x1 x1 nil
to-example₃ = refl

to-example₄ : to 4 ≡ x0 x0 x1 nil
to-example₄ = refl

from : Bin → ℕ
from nil = zero
from (x0 x) = 2 * from x
from (x1 x) = suc (2 * from x)

from-example₀ : from (x0 nil) ≡ 0
from-example₀ = refl

from-example₁ : from (x1 nil) ≡ 1
from-example₁ = refl

from-example₂ : from (x0 x1 nil) ≡ 2
from-example₂ = refl

from-example₃ : from (x1 x1 nil) ≡ 3
from-example₃ = refl

from-example₄ : from (x0 x0 x1 nil) ≡ 4
from-example₄ = refl
