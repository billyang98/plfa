module plfa.Connectives where

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl)
open Eq.≡-Reasoning
open import Data.Nat using (ℕ)
open import Function using (_∘_)
open import plfa.Isomorphism using (_≃_; _≲_; extensionality; _⇔_)
open plfa.Isomorphism.≃-Reasoning

-- Conjunction is product
data _×_ (A B : Set) : Set where
  ⟨_,_⟩ : A → B → A × B

proj₁ : {A B : Set} → A × B → A
proj₁ ⟨ x , y ⟩ = x

proj₂ : {A B : Set} → A × B → B
proj₂ ⟨ x , y ⟩ = y

record _×′_ (A B : Set) : Set where
  field
    proj₁′ : A
    proj₂′ : B

open _×′_

η-× : {A B : Set} (w : A × B) → ⟨ proj₁ w , proj₂ w ⟩ ≡ w
η-× ⟨ x , y ⟩ = refl

infixr 2 _×_

data Bool : Set where
  true : Bool
  false : Bool

data Tri : Set where
  aa : Tri
  bb : Tri
  cc : Tri

×-count : Bool × Tri → ℕ
×-count ⟨ true , aa ⟩ = 1
×-count ⟨ true , bb ⟩ = 2
×-count ⟨ true , cc ⟩ = 3
×-count ⟨ false , aa ⟩ = 4
×-count ⟨ false , bb ⟩ = 5
×-count ⟨ false , cc ⟩ = 6

×-comm : {A B : Set} → A × B ≃ B × A
×-comm =
  record
    { to = λ { ⟨ x , y ⟩ → ⟨ y , x ⟩ }
    ; from = λ { ⟨ y , x ⟩ → ⟨ x , y ⟩ }
    ; from∘to = λ { ⟨ x , y ⟩ → refl }
    ; to∘from = λ { ⟨ y , x ⟩ → refl }
    }

×-assoc : {A B C : Set} → (A × B) × C ≃ A × (B × C)
×-assoc =
  record
    { to = λ { ⟨ ⟨ x , y ⟩ , z ⟩ → ⟨ x , ⟨ y , z ⟩ ⟩ }
    ; from = λ { ⟨ x , ⟨ y , z ⟩ ⟩ → ⟨ ⟨ x , y ⟩ , z ⟩ }
    ; from∘to = λ { ⟨ ⟨ x , y ⟩ , z ⟩ → refl }
    ; to∘from = λ { ⟨ x , ⟨ y , z ⟩ ⟩  → refl }
    }

-- Exercise
⇔≃× : {A B : Set} → A ⇔ B ≃ (A → B) × (B → A)
⇔≃× =
  record
    { to = λ { record { to = A→B ; from = B→A } → ⟨ A→B , B→A ⟩ }
    ; from = λ { ⟨ A→B , B→A ⟩ → record { to = A→B ; from = B→A } }
    ; from∘to = λ { record { to = A→B ; from = B→A } → refl }
    ; to∘from = λ { ⟨ A→B , B→A ⟩ → refl }
    }
