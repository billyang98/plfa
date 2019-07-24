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
