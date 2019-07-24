module plfa.Equality where

-- Equality
data _≡_ {A : Set} (x : A) : A → Set where
  refl : x ≡ x

infix 4 _≡_

-- Equality is an equivalence relation
sym : {A : Set} {x y : A} → x ≡ y → y ≡ x
sym refl = refl

trans : {A : Set} {x y z : A} → x ≡ y → y ≡ z → x ≡ z
trans refl y≡z = y≡z

-- Congruence and substitution
cong : {A B : Set} (f : A → B) → {x y : A} → x ≡ y → f x ≡ f y
cong f refl = refl

cong₂ :
  {A B C : Set} (f : A → B → C) {u x : A} {v y : B} →
  u ≡ x →
  v ≡ y →
  f u v ≡ f x y
cong₂ f refl refl = refl

cong-app : {A B : Set} {f g : A → B} → f ≡ g → (x : A) → f x ≡ g x
cong-app refl x = refl

subst : {A : Set} {x y : A} (P : A → Set) → x ≡ y → P x → P y
subst P refl px = px

-- Chains of equations
module ≡-Reasoning {A : Set} where

  infix 1 begin_
  infixr 2 _≡⟨⟩_ _≡⟨_⟩_
  infix 3 _∎

  begin_ : {x y : A} → x ≡ y → x ≡ y
  begin x≡y = x≡y

  _≡⟨⟩_ : (x : A) {y : A} → x ≡ y → x ≡ y
  x ≡⟨⟩ x≡y = x≡y

  _≡⟨_⟩_ : (x : A) {y z : A} → x ≡ y → y ≡ z → x ≡ z
  _≡⟨_⟩_ x x≡y y≡z = trans x≡y y≡z

  _∎ : (x : A) → x ≡ x
  x ∎ = refl

open ≡-Reasoning

trans′ : {A : Set} {x y z : A} → x ≡ y → y ≡ z → x ≡ z
trans′ {A} {x} {y} {z} x≡y y≡z =
  begin
    x
  ≡⟨ x≡y ⟩
    y
  ≡⟨ y≡z ⟩
    z
  ∎

-- Chains of equations, another example
data ℕ : Set where
  zero : ℕ
  suc : ℕ → ℕ

{-# BUILTIN NATURAL ℕ #-}

_+_ : ℕ → ℕ → ℕ
zero + n = n
(suc m) + n = suc (m + n)

postulate
  +-identity : ∀ m → m + zero ≡ m
  +-suc : ∀ m n → m + suc n ≡ suc (m + n)

+-comm : ∀ m n → m + n ≡ n + m
+-comm zero n =
  begin
    zero + n
  ≡⟨⟩
    n
  ≡⟨ sym (+-identity n) ⟩
    n + zero
  ∎
+-comm (suc m) n =
  begin
    suc m + n
  ≡⟨⟩
    suc (m + n)
  ≡⟨ cong suc (+-comm m n) ⟩
    suc (n + m)
  ≡⟨ sym (+-suc n m) ⟩
    n + suc m
  ∎

-- Exercise ≤-Reasoning
data _≤_ : ℕ → ℕ → Set where
  z≤n : ∀ {n} → zero ≤ n
  s≤s : ∀ {m n} → m ≤ n → suc m ≤ suc n

module ≤-Reasoning where

  infix 1 start_
  infixr 2 _≤⟨⟩_ _≤⟨_⟩_
  infix 3 _◻

  start_ : ∀ {x y} → x ≤ y → x ≤ y
  start x≤y = x≤y

  _≤⟨⟩_ : ∀ x {y} → x ≤ y → x ≤ y
  x ≤⟨⟩ x≤y = x≤y

  _≤⟨_⟩_ : ∀ x {y z} → x ≤ y → y ≤ z → x ≤ z
  zero ≤⟨ z≤n ⟩ y≤z = z≤n
  suc m ≤⟨ s≤s x≤y ⟩ s≤s y≤z = s≤s (m ≤⟨ x≤y ⟩ y≤z)

  _◻ : ∀ x → x ≤ x
  zero ◻ = z≤n
  suc x ◻ = s≤s (x ◻)

open ≤-Reasoning

infixl 5 _+_
infix 4 _≤_

+-monoʳ-≤ : ∀ n p q → p ≤ q → n + p ≤ n + q
+-monoʳ-≤ zero p q p≤q =
  start
    zero + p
  ≤⟨ p≤q ⟩
    zero + q
  ◻
+-monoʳ-≤ (suc n) p q p≤q =
  start
    suc n + p
  ≤⟨⟩
    suc (n + p)
  ≤⟨ s≤s (+-monoʳ-≤ n p q p≤q) ⟩
    suc (n + q)
  ≤⟨⟩
    suc n + q
  ◻

≡→≤ : ∀ {x y} → x ≡ y → x ≤ y
≡→≤ refl = _ ◻

+-monoˡ-≤ : ∀ n m p → m ≤ n → m + p ≤ n + p
+-monoˡ-≤ n m zero m≤n =
  start
    m + zero
  ≤⟨ ≡→≤ (+-identity m) ⟩
    m
  ≤⟨ m≤n ⟩
    n
  ≤⟨ ≡→≤ (sym (+-identity n)) ⟩
    n + zero
  ◻
+-monoˡ-≤ n m (suc p) m≤n =
  start
    m + suc p
  ≤⟨ ≡→≤ (+-suc m p) ⟩
    suc (m + p)
  ≤⟨ s≤s (+-monoˡ-≤ n m p m≤n) ⟩
    suc (n + p)
  ≤⟨ ≡→≤ (sym (+-suc n p)) ⟩
    n + suc p
  ◻

+-mono-≤ : ∀ m n p q → m ≤ n → p ≤ q → m + p ≤ n + q
+-mono-≤ m n p q m≤n p≤q =
  start
    m + p
  ≤⟨ +-monoˡ-≤ n m p m≤n ⟩
    n + p
  ≤⟨ +-monoʳ-≤ n p q p≤q ⟩
    n + q
  ◻

-- Rewriting
data even : ℕ → Set
data odd : ℕ → Set

data even where
  even-zero : even zero
  even-suc : ∀ {n} → odd n → even (suc n)

data odd where
  odd-suc : ∀ {n} → even n → odd (suc n)

{-# BUILTIN EQUALITY _≡_ #-}

even-comm : ∀ m n → even (m + n) → even (n + m)
even-comm m n ev rewrite +-comm n m = ev

-- Multiple rewrites
+-comm′ : ∀ m n → m + n ≡ n + m
+-comm′ zero n rewrite +-identity n = refl
+-comm′ (suc m) n rewrite +-suc n m | +-comm′ m n = refl

-- Rewriting expanded
even-comm′ : ∀ m n → even (m + n) → even (n + m)
even-comm′ m n ev with m + n | +-comm m n
even-comm′ m n ev | .(n + m) | refl = ev

even-comm′′ : ∀ m n → even (m + n) → even (n + m)
even-comm′′ m n = subst even (+-comm m n)

-- Leibniz equality
_≐_ : {A : Set} (x y : A) → Set₁
_≐_ {A} x y = (P : A → Set) → P x → P y

foo : 3 ≐ 3
foo = λ P x → x

-- bar : 3 ≐ 5
-- bar = λ P x → {!!}

refl-≐ : {A : Set} {x : A} → x ≐ x
refl-≐ P Px = Px

trans-≐ : {A : Set} {x y z : A} → x ≐ y → y ≐ z → x ≐ z
trans-≐ x≐y y≐z P Px = y≐z P (x≐y P Px)

sym-≐ : {A : Set} {x y : A} → x ≐ y → y ≐ x
sym-≐ {A} {x} {y} x≐y P = Qy
  where
    Q : A → Set
    Q z = P z → P x

    Qx : Q x
    Qx = λ px → px

    Qy : Q y
    Qy = x≐y Q Qx

sym-≐′ : {A : Set} {x y : A} → x ≐ y → y ≐ x
sym-≐′ {A} {x} {y} x≐y P = x≐y (λ z → P z → P x) λ px → px

≡→≐ : {A : Set} {x y : A} → x ≡ y → x ≐ y
≡→≐ x≡y P = subst P x≡y

≐→≡ : {A : Set} {x y : A} → x ≐ y → x ≡ y
≐→≡ {A} {x} {y} x≐y = x≐y (x ≡_) refl

-- Universe polymorphism
open import Level using (Level; _⊔_) renaming (zero to lzero; suc to lsuc)

data _≡′_ {ℓ : Level} {A : Set ℓ} (x : A) : A → Set ℓ where
  refl′ : x ≡′ x

sym′ : {ℓ : Level} {A : Set ℓ} {x y : A} → x ≡′ y → y ≡′ x
sym′ refl′ = refl′

_≐′_ : {ℓ : Level} {A : Set ℓ} (x y : A) → Set (lsuc ℓ)
_≐′_ {ℓ} {A} x y = (P : A → Set ℓ) → P x → P y
