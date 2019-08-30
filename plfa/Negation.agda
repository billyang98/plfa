module plfa.Negation where

open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)
open import Data.Nat using (ℕ; zero; suc; _<_; z≤n; s≤s)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Sum using (_⊎_; inj₁; inj₂; swap)
open import Data.Product using (_×_; _,_)
open import Function using (_∘_)
open import plfa.Isomorphism using (_≃_; extensionality)
open import plfa.Connectives using (η-→)

-- Negation
¬_ : Set → Set
¬ A = A → ⊥

¬-elim : {A : Set} → ¬ A → A → ⊥
¬-elim ¬x x = ¬x x

infix 3 ¬_

¬¬-intro : {A : Set} → A → ¬ ¬ A
¬¬-intro x = λ ¬x → ¬x x

¬¬-intro′ : {A : Set} → A → ¬ ¬ A
¬¬-intro′ x ¬x = ¬x x

¬¬¬-elim : {A : Set} → ¬ ¬ ¬ A → ¬ A
¬¬¬-elim ¬¬¬x = λ x → ¬¬¬x (¬¬-intro x)

contraposition : {A B : Set} → (A → B) → (¬ B → ¬ A)
contraposition f ¬y x = ¬y (f x)

_≢_ : {A : Set} → A → A → Set
x ≢ y = ¬ (x ≡ y)

_ : 1 ≢ 2
_ = λ ()

peano : ∀ {m} → zero ≢ suc m
peano = λ ()

id : ⊥ → ⊥
id x = x

id′ : ⊥ → ⊥
id′ ()

id≡id′ : id ≡ id′
id≡id′ = extensionality λ ()

assimilation : {A : Set} (¬x ¬x′ : ¬ A) → ¬x ≡ ¬x′
assimilation ¬x ¬x′ = extensionality λ { x → ⊥-elim (¬x x) }

-- Exercise
<-irreflexive : ∀ n → ¬ (n < n)
<-irreflexive (suc n) (s≤s n<n) = <-irreflexive n n<n

-- Exercise
trichotomy :
  ∀ m n →
  (m < n × ¬ m ≡ n × ¬ n < m) ⊎
    (¬ m < n × m ≡ n × ¬ n < m) ⊎
      (¬ m < n × ¬ m ≡ n × n < m)
trichotomy zero zero = inj₂ (inj₁ ((λ ()) , refl , (λ ())))
trichotomy zero (suc n) = inj₁ (s≤s z≤n , (λ ()) , (λ ()))
trichotomy (suc m) zero = inj₂ (inj₂ ((λ ()) , (λ ()) , s≤s z≤n))
trichotomy (suc m) (suc n) with trichotomy m n
trichotomy (suc m) (suc n) | inj₁ (m<n , ¬m≡n , ¬m>n) =
  inj₁ (<-prf , ≡-prf , >-prf)
    where
      <-prf = s≤s m<n
      ≡-prf = λ { refl → ¬m≡n refl }
      >-prf = λ { (s≤s m>n) → ¬m>n m>n }
trichotomy (suc m) (suc n) | inj₂ (inj₁ (¬m<n , m≡n , ¬m>n)) =
  inj₂ (inj₁ (<-prf , ≡-prf , >-prf))
    where
      <-prf = λ { (s≤s m<n) → ¬m<n m<n }
      ≡-prf = cong suc m≡n
      >-prf = λ { (s≤s m>n) → ¬m>n m>n }
trichotomy (suc m) (suc n) | inj₂ (inj₂ (¬m<n , ¬m≡n , m>n)) =
  inj₂ (inj₂ (<-prf , ≡-prf , >-prf))
    where
      <-prf = λ { (s≤s m<n) → ¬m<n m<n }
      ≡-prf = λ { refl → ¬m≡n refl }
      >-prf = s≤s m>n

-- Exercise
×-≡ :
  {A B : Set} {x₁ x₂ : A} {y₁ y₂ : B} →
  x₁ ≡ x₂ →
  y₁ ≡ y₂ →
  (x₁ , y₁) ≡ (x₂ , y₂)
×-≡ refl refl = refl

⊎-dual-× : {A B : Set} → ¬ (A ⊎ B) ≃ (¬ A) × (¬ B)
⊎-dual-× =
  record
    { to = λ ¬[x+y] → (λ x → ¬[x+y] (inj₁ x)) , (λ y → ¬[x+y] (inj₂ y))
    ; from = λ { (¬x , ¬y) (inj₁ x) → ¬x x ; (¬x , ¬y) (inj₂ y) → ¬y y }
    ; from∘to = λ ¬[x+y] → extensionality λ { (inj₁ x) → refl ; (inj₂ y) → refl }
    ; to∘from = λ { (¬x , ¬y) → ×-≡ (η-→ ¬x) (η-→ ¬y) }
    }

×-not-quite-dual-⊎ : {A B : Set} → (¬ A) ⊎ (¬ B) → ¬ (A × B)
×-not-quite-dual-⊎ (inj₁ ¬x) (x , y) = ¬x x
×-not-quite-dual-⊎ (inj₂ ¬y) (x , y) = ¬y y

-- Excluded middle is irrefutable
postulate
  em : {A : Set} → A ⊎ ¬ A

em-irrefutable : {A : Set} → ¬ ¬ (A ⊎ ¬ A)
em-irrefutable = λ k → k (inj₂ (λ x → k (inj₁ x)))

-- Exercise: Classical
em→dne : {A : Set} → A ⊎ ¬ A → ¬ ¬ A → A
em→dne (inj₁ x) ¬¬x = x
em→dne (inj₂ ¬x) ¬¬x = ⊥-elim (¬¬x ¬x)

em→peirce : {A B : Set} → A ⊎ ¬ A → ((A → B) → A) → A
em→peirce (inj₁ x) k = x
em→peirce (inj₂ ¬x) k = k λ x → ⊥-elim (¬x x)

em→¬⊎ : {A B : Set} → A ⊎ ¬ A → (A → B) → ¬ A ⊎ B
em→¬⊎ (inj₁ x) f = inj₂ (f x)
em→¬⊎ (inj₂ ¬x) f = inj₁ ¬x

em→deMorgan : ({A : Set} → A ⊎ ¬ A) → {A B : Set} → ¬ (¬ A × ¬ B) → A ⊎ B
em→deMorgan lem {A} {B} d with lem {A} | lem {B}
em→deMorgan lem {A} {B} d | inj₁ x | y⊎¬y = inj₁ x
em→deMorgan lem {A} {B} d | inj₂ ¬x | inj₁ y = inj₂ y
em→deMorgan lem {A} {B} d | inj₂ ¬x | inj₂ ¬y = ⊥-elim (d (¬x , ¬y))

dne→em : ({A : Set} → ¬ ¬ A → A) → {A : Set} → A ⊎ ¬ A
dne→em dne = dne em-irrefutable

dne→peirce : {A B : Set} → (¬ ¬ A → A) → ((A → B) → A) → A
dne→peirce dne k = dne λ ¬x → ¬x (k λ x → ⊥-elim (¬x x))

peirce→em : ({A B : Set} → (((A → B) → A) → A)) → {A : Set} → A ⊎ ¬ A
peirce→em p = p λ ¬em → ⊥-elim (em-irrefutable ¬em)

¬⊎→em : ({A B : Set} → ((A → B) → ¬ A ⊎ B)) → {A : Set} → A ⊎ ¬ A
¬⊎→em ¬⊎ = swap (¬⊎ λ x → x)

deMorgan→em : ({A B : Set} → ¬ (¬ A × ¬ B) → A ⊎ B) → {A : Set} → A ⊎ ¬ A
deMorgan→em dem = dem λ { (¬x , ¬¬x) → ¬¬x ¬x }

peirce→deMorgan :
  ({A B : Set} → (((A → B) → A) → A)) →
  {A B : Set} → ¬ (¬ A × ¬ B) → A ⊎ B
peirce→deMorgan = em→deMorgan ∘ peirce→em

-- Exercise: Stable
Stable : Set → Set
Stable A = ¬ ¬ A → A

¬-Stable : {A : Set} → Stable (¬ A)
¬-Stable = ¬¬¬-elim

×-Stable : {A B : Set} → Stable A → Stable B → Stable (A × B)
×-Stable ¬¬x→x ¬¬y→y ¬¬xy = (xPrf , yPrf)
  where
    xPrf = ¬¬x→x (λ ¬x → ¬¬xy λ { (x , y) → ¬x x })
    yPrf = ¬¬y→y (λ ¬y → ¬¬xy λ { (x , y) → ¬y y })
