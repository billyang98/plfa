module plfa.Isomorphism where

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong; cong-app; sym; trans)
open Eq.≡-Reasoning
open import Data.Nat using (ℕ; zero; suc; _+_; _*_)
open import Data.Nat.Properties using (+-comm; +-suc)
open import Level using (Level; _⊔_) renaming (zero to lzero; suc to lsuc)
open import Function using (id)

-- Function composition
_∘_ : {A B C : Set} → (B → C) → (A → B) → (A → C)
(g ∘ f) x = g (f x)

_∘′_ : {A B C : Set} → (B → C) → (A → B) → (A → C)
g ∘′ f = λ x → g (f x)

-- Extensionality
postulate
  extensionality : {A B : Set} {f g : A → B} → ((x : A) → f x ≡ g x) → f ≡ g

_+′_ : ℕ → ℕ → ℕ
m +′ zero = m
m +′ suc n = suc (m +′ n)

same-app : ∀ m n → m +′ n ≡ m + n
same-app m n rewrite +-comm m n = helper m n
  where
    helper : ∀ m n → m +′ n ≡ n + m
    helper m zero = refl
    helper m (suc n) = cong suc (helper m n)

same : _+′_ ≡ _+_
same = extensionality λ m → extensionality λ n → same-app m n

-- Isomorphism
infix 0 _≃_

record _≃_ (A B : Set) : Set where
  field
    to : A → B
    from : B → A
    from∘to : (x : A) → from (to x) ≡ x
    to∘from : (y : B) → to (from y) ≡ y

open _≃_

-- Isomorphism is an equivalence
record Equiv {ℓ : Level} (_~_ : (A B : Set) → Set ℓ) : Set (lsuc ℓ) where
  field
    equiv-refl : {A : Set} → A ~ A
    equiv-sym : {A B : Set} → A ~ B → B ~ A
    equiv-trans : {A B C : Set} → A ~ B → B ~ C → A ~ C

open Equiv

≡-Equiv : Equiv _≡_
≡-Equiv =
  record
    { equiv-refl = refl
    ; equiv-sym = sym
    ; equiv-trans = trans
    }

≃-refl : {A : Set} → A ≃ A
≃-refl =
  record
    { to = λ x → x
    ; from = λ y → y
    ; from∘to = λ x → refl
    ; to∘from = λ y → refl
    }

≃-sym : {A B : Set} → A ≃ B → B ≃ A
≃-sym A≃B =
  record
    { to = from A≃B
    ; from = to A≃B
    ; from∘to = to∘from A≃B
    ; to∘from = from∘to A≃B
    }

≃-trans : {A B C : Set} → A ≃ B → B ≃ C → A ≃ C
≃-trans A≃B B≃C =
  record
    { to = to B≃C ∘ to A≃B
    ; from = from A≃B ∘ from B≃C
    ; from∘to = λ x →
        begin
          ((from A≃B ∘ from B≃C) ∘ (to B≃C ∘ to A≃B)) x
        ≡⟨⟩
          from A≃B (from B≃C (to B≃C (to A≃B x)))
        ≡⟨ cong (from A≃B) (from∘to B≃C (to A≃B x)) ⟩
          from A≃B (to A≃B x)
        ≡⟨ from∘to A≃B x ⟩
          x
        ∎
    ; to∘from = λ y →
        begin
          ((to B≃C ∘ to A≃B) ∘ (from A≃B ∘ from B≃C)) y
        ≡⟨⟩
          to B≃C (to A≃B (from A≃B (from B≃C y)))
        ≡⟨ cong (to B≃C) (to∘from A≃B (from B≃C y)) ⟩
          to B≃C (from B≃C y)
        ≡⟨ to∘from B≃C y ⟩
          y
        ∎
    }

≃-Equiv : Equiv _≃_
≃-Equiv =
  record
  { equiv-refl = ≃-refl
  ; equiv-sym = ≃-sym
  ; equiv-trans = ≃-trans
  }

-- Equational reasoning for isomorphism
module ≃-Reasoning where

  infix 1 ≃-begin_
  infixr 2 _≃⟨_⟩_
  infix 3 _≃-∎

  ≃-begin_ : {A B : Set} → A ≃ B → A ≃ B
  ≃-begin A≃B = A≃B

  _≃⟨_⟩_ : (A : Set) {B C : Set} → A ≃ B → B ≃ C → A ≃ C
  A ≃⟨ A≃B ⟩ B≃C = ≃-trans A≃B B≃C

  _≃-∎ : (A : Set) → A ≃ A
  A ≃-∎ = ≃-refl

open ≃-Reasoning

-- Embedding
infix 0 _≲_

record _≲_ (A B : Set) : Set where
  field
    to : A → B
    from : B → A
    from∘to : (x : A) → from (to x) ≡ x

open _≲_

≲-refl : {A : Set} → A ≲ A
≲-refl = record { to = λ x → x ; from = λ y → y ; from∘to = λ x → refl }

≲-trans : {A B C : Set} → A ≲ B → B ≲ C → A ≲ C
≲-trans A≲B B≲C =
  record
    { to = λ x → to B≲C (to A≲B x)
    ; from = λ y → from A≲B (from B≲C y)
    ; from∘to = λ x →
        begin
          from A≲B (from B≲C (to B≲C (to A≲B x)))
        ≡⟨ cong (from A≲B) (from∘to B≲C (to A≲B x)) ⟩
          from A≲B (to A≲B x)
        ≡⟨ from∘to A≲B x ⟩
          x
        ∎
    }

≲-antisym :
  {A B : Set} →
  (A≲B : A ≲ B) →
  (B≲A : B ≲ A) →
  (to A≲B ≡ from B≲A) →
  (from A≲B ≡ to B≲A) →
  A ≃ B
≲-antisym A≲B B≲A to≡from from≡to =
  record
    { to = to A≲B
    ; from = from A≲B
    ; from∘to = from∘to A≲B
    ; to∘from = to∘from-proof
    }
  where
    to∘from-proof : ∀ y → to A≲B (from A≲B y) ≡ y
    to∘from-proof y rewrite from≡to | to≡from = from∘to B≲A y

-- Equational reasoning for embedding
module ≲-Reasoning where

  infix 1 ≲-begin_
  infixr 2 _≲⟨_⟩_
  infix 3 _≲-∎

  ≲-begin_ : {A B : Set} → A ≲ B → A ≲ B
  ≲-begin A≲B = A≲B

  _≲⟨_⟩_ : (A : Set) {B C : Set} → A ≲ B → B ≲ C → A ≲ C
  A ≲⟨ A≲B ⟩ B≲C = ≲-trans A≲B B≲C

  _≲-∎ : (A : Set) → A ≲ A
  A ≲-∎ = ≲-refl

open ≲-Reasoning

-- Exercises
≃-implies-≲ : {A B : Set} → A ≃ B → A ≲ B
≃-implies-≲ A≃B =
  record { to = to A≃B ; from = from A≃B ; from∘to = from∘to A≃B }

record _⇔_ (A B : Set) : Set where
  field
    to : A → B
    from : B → A

⇔-Equiv : Equiv _⇔_
⇔-Equiv =
  record
    { equiv-refl = record { to = id ; from = id }
    ; equiv-sym = λ A⇔B → record { to = _⇔_.from A⇔B ; from = _⇔_.to A⇔B }
    ; equiv-trans = λ A⇔B B⇔C →
        record
          { to = λ A → _⇔_.to B⇔C (_⇔_.to A⇔B A)
          ; from = λ C → _⇔_.from A⇔B (_⇔_.from B⇔C C)
          }
    }

data Bin : Set where
  nil : Bin
  x0_ : Bin → Bin
  x1_ : Bin → Bin

inc : Bin → Bin
inc nil = x1 nil
inc (x0 x) = x1 x
inc (x1 x) = x0 (inc x)

to-Bin : ℕ → Bin
to-Bin zero = x0 nil
to-Bin (suc n) = inc (to-Bin n)

from-Bin : Bin → ℕ
from-Bin nil = zero
from-Bin (x0 x) = 2 * from-Bin x
from-Bin (x1 x) = suc (2 * from-Bin x)

2*suc : ∀ n → 2 * suc n ≡ suc (suc (2 * n))
2*suc n =
  begin
    2 * suc n
  ≡⟨⟩
    suc (suc zero) * suc n
  ≡⟨⟩
    suc n + suc zero * suc n
  ≡⟨⟩
    suc n + (suc n + zero * suc n)
  ≡⟨⟩
    suc n + (suc n + zero)
  ≡⟨⟩
    suc (n + (suc n + zero))
  ≡⟨⟩
    suc (n + suc (n + zero))
  ≡⟨ cong suc (+-suc n (n + zero)) ⟩
    suc (suc (n + (n + zero)))
  ≡⟨⟩
    suc (suc (2 * n))
  ∎

inc-suc : ∀ x → from-Bin (inc x) ≡ suc (from-Bin x)
inc-suc nil =
  begin
    from-Bin (inc nil)
  ≡⟨⟩
    from-Bin (x1 nil)
  ≡⟨⟩
    suc (2 * from-Bin nil)
  ≡⟨⟩
    suc (2 * 0)
  ≡⟨⟩
    suc zero
  ≡⟨⟩
    suc (from-Bin nil)
  ∎
inc-suc (x0 x) =
  begin
    from-Bin (inc (x0 x))
  ≡⟨⟩
    from-Bin (x1 x)
  ≡⟨⟩
    suc (2 * from-Bin x)
  ≡⟨⟩
    suc (from-Bin (x0 x))
  ∎
inc-suc (x1 x) =
  begin
    from-Bin (inc (x1 x))
  ≡⟨⟩
    from-Bin (x0 (inc x))
  ≡⟨⟩
    2 * from-Bin (inc x)
  ≡⟨ cong (_*_ 2) (inc-suc x) ⟩
    2 * suc (from-Bin x)
  ≡⟨ 2*suc (from-Bin x) ⟩
    suc (suc (2 * from-Bin x))
  ≡⟨⟩
    suc (from-Bin (x1 x))
  ∎

from-to-id : ∀ n → from-Bin (to-Bin n) ≡ n
from-to-id zero =
  begin
    from-Bin (to-Bin 0)
  ≡⟨⟩
    from-Bin (x0 nil)
  ≡⟨⟩
    2 * from-Bin nil
  ≡⟨⟩
    2 * 0
  ≡⟨⟩
    0
  ∎
from-to-id (suc n) =
  begin
    from-Bin (to-Bin (suc n))
  ≡⟨⟩
    from-Bin (inc (to-Bin n))
  ≡⟨ inc-suc (to-Bin n) ⟩
    suc (from-Bin (to-Bin n))
  ≡⟨ cong suc (from-to-id n) ⟩
    suc n
  ∎

ℕ≲Bin : ℕ ≲ Bin
ℕ≲Bin = record { to = to-Bin ; from = from-Bin ; from∘to = from-to-id }
