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

-- Truth is unit
data ⊤ : Set where
  tt : ⊤

η-⊤ : (w : ⊤) → tt ≡ w
η-⊤ tt = refl

⊤-count : ⊤ → ℕ
⊤-count tt = 1

⊤-identityˡ : {A : Set} → ⊤ × A ≃ A
⊤-identityˡ =
  record
    { to = λ { ⟨ t , x ⟩ → x }
    ; from = λ { x → ⟨ tt , x ⟩ }
    ; from∘to = λ { ⟨ tt , x ⟩ → refl }
    ; to∘from = λ { x → refl }
    }

⊤-identityʳ : {A : Set} → (A × ⊤) ≃ A
⊤-identityʳ {A} =
  ≃-begin
    (A × ⊤)
  ≃⟨ ×-comm ⟩
    (⊤ × A)
  ≃⟨ ⊤-identityˡ ⟩
    A
  ≃-∎

-- Disjunction is sum
data _⊎_ (A B : Set) : Set where
  inj₁ : A → A ⊎ B
  inj₂ : B → A ⊎ B

case-⊎ : {A B C : Set} → (A → C) → (B → C) → A ⊎ B → C
case-⊎ f g (inj₁ x) = f x
case-⊎ f g (inj₂ y) = g y

η-⊎ : {A B : Set} (w : A ⊎ B) → case-⊎ inj₁ inj₂ w ≡ w
η-⊎ (inj₁ x) = refl
η-⊎ (inj₂ y) = refl

uniq-⊎ :
  {A B C : Set} (h : A ⊎ B → C) (w : A ⊎ B) →
  case-⊎ (h ∘ inj₁) (h ∘ inj₂) w ≡ h w
uniq-⊎ h (inj₁ x) = refl
uniq-⊎ h (inj₂ y) = refl

infix 1 _⊎_

⊎-count : Bool ⊎ Tri → ℕ
⊎-count (inj₁ true) = 1
⊎-count (inj₁ false) = 2
⊎-count (inj₂ aa) = 3
⊎-count (inj₂ bb) = 4
⊎-count (inj₂ cc) = 5

-- Exercise
⊎-comm : {A B : Set} → A ⊎ B ≃ B ⊎ A
⊎-comm =
  record
    { to = λ { (inj₁ x) → inj₂ x ; (inj₂ y) → inj₁ y }
    ; from = λ { (inj₁ y) → inj₂ y ; (inj₂ x) → inj₁ x }
    ; from∘to = λ { (inj₁ x) → refl ; (inj₂ y) → refl }
    ; to∘from = λ { (inj₁ y) → refl ; (inj₂ x) → refl }
    }

-- Exercise
⊎-assoc : {A B C : Set} → (A ⊎ B) ⊎ C ≃ A ⊎ (B ⊎ C)
⊎-assoc =
  record
    { to = λ
      { (inj₁ (inj₁ x)) → inj₁ x
      ; (inj₁ (inj₂ y)) → inj₂ (inj₁ y)
      ; (inj₂ z) → inj₂ (inj₂ z)
      }
    ; from = λ
      { (inj₁ x) → inj₁ (inj₁ x)
      ; (inj₂ (inj₁ y)) → inj₁ (inj₂ y)
      ; (inj₂ (inj₂ z)) → inj₂ z
      }
    ; from∘to = λ
      { (inj₁ (inj₁ x)) → refl
      ; (inj₁ (inj₂ x)) → refl
      ; (inj₂ x) → refl
      }
    ; to∘from = λ
      { (inj₁ x) → refl
      ; (inj₂ (inj₁ x)) → refl
      ; (inj₂ (inj₂ x)) → refl
      }
    }

-- False is empty
data ⊥ : Set where

⊥-elim : {A : Set} → ⊥ → A
⊥-elim ()

uniq-⊥ : {C : Set} (h : ⊥ → C) (w : ⊥) → ⊥-elim w ≡ h w
uniq-⊥ h ()

⊥-count : ⊥ → ℕ
⊥-count ()

-- Exercise
⊥-identityˡ : {A : Set} → ⊥ ⊎ A ≃ A
⊥-identityˡ =
  record
    { to = λ { (inj₂ x) → x }
    ; from = λ { x → inj₂ x }
    ; from∘to = λ { (inj₂ x) → refl }
    ; to∘from = λ x → refl
    }

-- Exercise
⊥-identityʳ : {A : Set} → A ⊎ ⊥ ≃ A
⊥-identityʳ {A} =
  ≃-begin
    (A ⊎ ⊥)
  ≃⟨ ⊎-comm ⟩
    (⊥ ⊎ A)
  ≃⟨ ⊥-identityˡ ⟩
    A
  ≃-∎

-- Implication is function
→-elim : {A B : Set} → (A → B) → A → B
→-elim L M = L M

η-→ : {A B : Set} (f : A → B) → (λ (x : A) → f x) ≡ f
η-→ f = refl

→-count : (Bool → Tri) → ℕ
→-count f with f true | f false
→-count f | aa | aa = 1
→-count f | aa | bb = 2
→-count f | aa | cc = 3
→-count f | bb | aa = 4
→-count f | bb | bb = 5
→-count f | bb | cc = 6
→-count f | cc | aa = 7
→-count f | cc | bb = 8
→-count f | cc | cc = 9

currying : {A B C : Set} → (A → B → C) ≃ (A × B → C)
currying =
  record
    { to = λ { f ⟨ x , y ⟩ → f x y }
    ; from = λ { g x y → g ⟨ x , y ⟩ }
    ; from∘to = λ f → refl
    ; to∘from = λ g → extensionality λ { ⟨ x , y ⟩ → refl }
    }

→-distrib-⊎ : {A B C : Set} → (A ⊎ B → C) ≃ ((A → C) × (B → C))
→-distrib-⊎ =
  record
    { to = λ { f → ⟨ f ∘ inj₁ , f ∘ inj₂ ⟩ }
    ; from = λ { ⟨ g , h ⟩ (inj₁ x) → g x ; ⟨ g , h ⟩ (inj₂ y) → h y }
    ; from∘to = λ { f → extensionality λ { (inj₁ x) → refl ; (inj₂ y) → refl } }
    ; to∘from = λ { ⟨ g , h ⟩ → refl }
    }

→-distrib-× : {A B C : Set} → (A → B × C) ≃ (A → B) × (A → C)
→-distrib-× =
  record
    { to = λ { f → ⟨ proj₁ ∘ f , proj₂ ∘ f ⟩ }
    ; from = λ { ⟨ g , h ⟩ x → ⟨ g x , h x ⟩ }
    ; from∘to = λ { f → extensionality (η-× ∘ f) }
    ; to∘from = λ { ⟨ g , h ⟩ → refl }
    }

-- Distribution
×-distrib-⊎ : {A B C : Set} → (A ⊎ B) × C ≃ (A × C) ⊎ (B × C)
×-distrib-⊎ =
  record
    { to = λ
      { ⟨ inj₁ x , z ⟩ → inj₁ ⟨ x , z ⟩
      ; ⟨ inj₂ y , z ⟩ → inj₂ ⟨ y , z ⟩
      }
    ; from = λ
      { (inj₁ ⟨ x , z ⟩) → ⟨ inj₁ x , z ⟩
      ; (inj₂ ⟨ y , z ⟩) → ⟨ inj₂ y , z ⟩
      }
    ; from∘to = λ { ⟨ inj₁ x , z ⟩ → refl ; ⟨ inj₂ y , z ⟩ → refl }
    ; to∘from = λ { (inj₁ ⟨ x , z ⟩) → refl ; (inj₂ ⟨ y , z ⟩) → refl }
    }

⊎-distrib-× : {A B C : Set} → (A × B) ⊎ C ≲ (A ⊎ C) × (B ⊎ C)
⊎-distrib-× =
  record
    { to = λ
      { (inj₁ ⟨ x , y ⟩) → ⟨ inj₁ x , inj₁ y ⟩
      ; (inj₂ z) → ⟨ inj₂ z , inj₂ z ⟩
      }
    ; from = λ
      { ⟨ inj₁ x , inj₁ y ⟩ → inj₁ ⟨ x , y ⟩
      ; ⟨ inj₁ x , inj₂ z ⟩ → inj₂ z
      ; ⟨ inj₂ z , _ ⟩ → inj₂ z
      }
    ; from∘to = λ { (inj₁ ⟨ x , y ⟩) → refl ; (inj₂ z) → refl }
    }

-- Exercise
⊎-weak-× : {A B C : Set} → (A ⊎ B) × C → A ⊎ (B × C)
⊎-weak-× ⟨ inj₁ x , z ⟩ = inj₁ x
⊎-weak-× ⟨ inj₂ y , z ⟩ = inj₂ ⟨ y , z ⟩

-- The corresponding distributive law is ×-distrib-⊎.
-- This relates to the weak version in that it doesn't throw away the value
-- for C that gets paired with A. This allows it to be an isomorphism.

-- Exercise
⊎×-implies-×⊎ : {A B C D : Set} → (A × B) ⊎ (C × D) → (A ⊎ C) × (B ⊎ D)
⊎×-implies-×⊎ (inj₁ ⟨ x , y ⟩) = ⟨ inj₁ x , inj₁ y ⟩
⊎×-implies-×⊎ (inj₂ ⟨ z , w ⟩) = ⟨ inj₂ z , inj₂ w ⟩

-- ×⊎-implies-⊎x : {A B C D : Set} → (A ⊎ C) × (B ⊎ D) → (A × B) ⊎ (C × D)
-- ×⊎-implies-⊎x ⟨ inj₁ x , inj₁ y ⟩ = inj₁ ⟨ x , y ⟩
-- ×⊎-implies-⊎x ⟨ inj₁ x , inj₂ w ⟩ = {!!}
-- ×⊎-implies-⊎x ⟨ inj₂ z , inj₁ y ⟩ = {!!}
-- ×⊎-implies-⊎x ⟨ inj₂ z , inj₂ w ⟩ = inj₂ ⟨ z , w ⟩

-- The converse is impossible in the above incomplete cases,
-- where we have one side each of (A × B) and (C × D), but
-- both sides of one of them are needed.
