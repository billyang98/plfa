module plfa.Isomorphism where

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong; cong-app)
open Eq.≡-Reasoning
open import Data.Nat using (ℕ; zero; suc; _+_)
open import Data.Nat.Properties using (+-comm)

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
record Equiv (_~_ : (A B : Set) → Set) : Set₁ where
  field
    equiv-refl : {A : Set} → A ~ A
    equiv-sym : {A B : Set} → A ~ B → B ~ A
    equiv-trans : {A B C : Set} → A ~ B → B ~ C → A ~ C

open Equiv

≃-Equiv : Equiv _≃_
≃-Equiv =
  record
  { equiv-refl = λ {A} →
      record
      { to = λ z → z
      ; from = λ z → z
      ; from∘to = λ x → refl
      ; to∘from = λ y → refl
      }
  ; equiv-sym =
      {!!}
  ; equiv-trans =
      {!!}
  }
