module plfa.Relations where

-- Imports
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong)
open import Data.Nat using (ℕ; zero; suc; _+_; _*_)
open import Data.Nat.Properties using (+-comm; *-comm)

-- Defining relations
data _≤_ : ℕ → ℕ → Set where
  z≤n : ∀ {n} → zero ≤ n
  s≤s : ∀ {m n} → m ≤ n → suc m ≤ suc n

_ : 2 ≤ 4
_ = s≤s (s≤s z≤n)

-- Implicit arguments
_ : 2 ≤ 4
_ = s≤s {1} {3} (s≤s {0} {2} (z≤n {2}))

_ : 2 ≤ 4
_ = s≤s {m = 1} {n = 3} (s≤s {m = 0} {n = 2} (z≤n {n = 2}))

_ : 2 ≤ 4
_ = s≤s {n = 3} (s≤s {n = 2} z≤n)

-- Precedence
infix 4 _≤_

-- Inversion
inv-s≤s : ∀ {m n} → suc m ≤ suc n → m ≤ n
inv-s≤s (s≤s m≤n) = m≤n

inv-z≤n : ∀ {m} → m ≤ zero → m ≡ zero
inv-z≤n z≤n = refl

-- Exercise orderings
-- Preorder that is not a partial order:
-- A relation _connected_ in directed graphs, such that
-- x connected y holds of two nodes x and y if there's
-- a directed path from x to y. This is reflexive and
-- transitive, but if x connected y and y connected x,
-- it's not necessarily the case that x and y are the same node.

-- Partial order that is not total:
-- The subset relation (_⊆_)

-- Reflexivity
≤-refl : ∀ {n} → n ≤ n
≤-refl {zero} = z≤n
≤-refl {suc n} = s≤s ≤-refl

-- Transitivity
≤-trans : ∀ {m n p} → m ≤ n → n ≤ p → m ≤ p
≤-trans z≤n n≤p = z≤n
≤-trans (s≤s m≤n) (s≤s n≤p) = s≤s (≤-trans m≤n n≤p)

-- Anti-symmetry
≤-antisym : ∀ {m n} → m ≤ n → n ≤ m → m ≡ n
≤-antisym z≤n z≤n = refl
≤-antisym (s≤s m≤n) (s≤s n≤m) = cong suc (≤-antisym m≤n n≤m)

-- Exercise ≤-antisym-cases
-- It's okay to omit the cases where one argument is z≤n and one argument
-- is s≤s because they are impossible: if we have (z≤n : m ≤ n) and
-- (s≤s : n ≤ m), then m must be both zero and suc _, which is not allowed.
-- And if it's the other way around, then the same holds for n.

-- Total
data Total (m n : ℕ) : Set where
  forward : m ≤ n → Total m n
  flipped : n ≤ m → Total m n

≤-total : ∀ m n → Total m n
≤-total zero n = forward z≤n
≤-total (suc m) zero = flipped z≤n
≤-total (suc m) (suc n) with ≤-total m n
... | forward m≤n = forward (s≤s m≤n)
... | flipped n≤m = flipped (s≤s n≤m)

-- Monotonicity
+-monoʳ-≤ : ∀ n p q → p ≤ q → n + p ≤ n + q
+-monoʳ-≤ zero p q p≤q = p≤q
+-monoʳ-≤ (suc n) p q p≤q = s≤s (+-monoʳ-≤ n p q p≤q)

+-monoˡ-≤ : ∀ m n p → m ≤ n → m + p ≤ n + p
+-monoˡ-≤ m n p m≤n rewrite +-comm m p | +-comm n p = +-monoʳ-≤ p m n m≤n

+-mono-≤ : ∀ m n p q → m ≤ n → p ≤ q → m + p ≤ n + q
+-mono-≤ m n p q m≤n p≤q = ≤-trans (+-monoˡ-≤ m n p m≤n) (+-monoʳ-≤ n p q p≤q)

-- Exercise *-mono-≤
*-monoʳ-≤ : ∀ n p q → p ≤ q → n * p ≤ n * q
*-monoʳ-≤ zero p q p≤q = z≤n
*-monoʳ-≤ (suc n) p q p≤q =
  +-mono-≤ p q (n * p) (n * q) p≤q (*-monoʳ-≤ n p q p≤q)

*-monoˡ-≤ : ∀ m n p → m ≤ n → m * p ≤ n * p
*-monoˡ-≤ m n p m≤n rewrite *-comm m p | *-comm n p = *-monoʳ-≤ p m n m≤n

*-mono-≤ : ∀ m n p q → m ≤ n → p ≤ q → m * p ≤ n * q
*-mono-≤ m n p q m≤n p≤q = ≤-trans (*-monoˡ-≤ m n p m≤n) (*-monoʳ-≤ n p q p≤q)

-- Strict inequality
infix 4 _<_

data _<_ : ℕ → ℕ → Set where
  z<s : ∀ {n} → zero < suc n
  s<s : ∀ {m n} → m < n → suc m < suc n

-- Exercise <-trans
<-trans : ∀ {m n p} → m < n → n < p → m < p
<-trans z<s (s<s n<p) = z<s
<-trans (s<s m<n) (s<s n<p) = s<s (<-trans m<n n<p)

-- Exercise trichotomy
data Trichotomous (n m : ℕ) : Set where
  less : n < m → Trichotomous n m
  same : n ≡ m → Trichotomous n m
  more : m < n → Trichotomous n m

<-trichotomous : ∀ n m → Trichotomous n m
<-trichotomous zero zero = same refl
<-trichotomous zero (suc m) = less z<s
<-trichotomous (suc n) zero = more z<s
<-trichotomous (suc n) (suc m) with <-trichotomous n m
... | less n<m = less (s<s n<m)
... | same n≡m = same (cong suc n≡m)
... | more m<n = more (s<s m<n)

-- Exercise +-mono-<
+-monoʳ-< : ∀ n p q → p < q → n + p < n + q
+-monoʳ-< zero p q p<q = p<q
+-monoʳ-< (suc n) p q p<q = s<s (+-monoʳ-< n p q p<q)

+-monoˡ-< : ∀ m n p → m < n → m + p < n + p
+-monoˡ-< m n p m<n rewrite +-comm m p | +-comm n p = +-monoʳ-< p m n m<n

+-mono-< : ∀ m n p q → m < n → p < q → m + p < n + q
+-mono-< m n p q m<n p<q = <-trans (+-monoˡ-< m n p m<n) (+-monoʳ-< n p q p<q)

-- Exercise ≤-iff-<
≤→< : ∀ {m n} → suc m ≤ n → m < n
≤→< {zero} {suc n} sm≤n = z<s
≤→< {suc m} {suc n} (s≤s sm≤n) = s<s (≤→< sm≤n)

<→≤ : ∀ {m n} → m < n → suc m ≤ n
<→≤ {zero} {suc n} z<s = s≤s z≤n
<→≤ {suc m} {suc n} (s<s m<n) = s≤s (<→≤ m<n)

-- Exercise <-trans-revisited
n≤sn : ∀ {n} → n ≤ suc n
n≤sn {n} = +-monoˡ-≤ 0 1 n z≤n

<-trans′ : ∀ {m n p} → m < n → n < p → m < p
<-trans′ m<n n<p = ≤→< (≤-trans (<→≤ m<n) (≤-trans n≤sn (<→≤ n<p)))
