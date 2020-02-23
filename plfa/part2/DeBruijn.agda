module plfa.part2.DeBruijn where

-- Imports
open import Agda.Builtin.FromNat using (Number)
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Fin using (Fin) renaming (zero to FZ; suc to FS)
import Data.Fin.Literals as FinLit
open import Data.Nat using (ℕ; zero; suc; _<_; _≤_; z≤n; s≤s)
import Data.Nat.Literals as NatLit
open import Data.Unit
open import Relation.Nullary using (¬_)

instance
  NumNat : Number ℕ
  NumNat = NatLit.number

  NumFin : ∀ {n} → Number (Fin n)
  NumFin {n} = FinLit.number n

-- Introduction
-- A second example
-- Order of presentation
-- Syntax

infix  4 _⊢_
infix  4 _∋_
infixl 5 _,_

infixr 7 _⇒_

infix  5 ƛ_
infix  5 μ_
infixl 7 _·_
infix  8 `suc_
infix  9 `_
infix  9 S_
infix  9 #_

-- Types
data Type : Set where
  _⇒_ : Type → Type → Type
  `ℕ : Type

-- Contexts
data Context : ℕ → Set where
  ∅ : Context 0
  _,_ : ∀ {n} → Context n → Type → Context (suc n)

_ : Context 2
_ = ∅ , `ℕ ⇒ `ℕ , `ℕ

-- Variables and the lookup judgment
data _∋_ : ∀ {n} → Context n → Type → Set where
  Z : ∀ {n A} → {Γ : Context n} → Γ , A ∋ A
  S_ : ∀ {n A B} → {Γ : Context n} → Γ ∋ A → Γ , B ∋ A

_ : ∅ , `ℕ ⇒ `ℕ , `ℕ ∋ `ℕ
_ = Z

_ : ∅ , `ℕ ⇒ `ℕ , `ℕ ∋ `ℕ ⇒ `ℕ
_ = S Z

-- Terms and the typing judgment
data _⊢_ {n} (Γ : Context n) : Type → Set where
  `_ : ∀ {A} → Γ ∋ A → Γ ⊢ A
  ƛ_ : ∀ {A B} → Γ , A ⊢ B → Γ ⊢ A ⇒ B
  _·_ : ∀ {A B} → Γ ⊢ A ⇒ B → Γ ⊢ A → Γ ⊢ B
  `zero : Γ ⊢ `ℕ
  `suc_ : Γ ⊢ `ℕ → Γ ⊢ `ℕ
  case : ∀ {A} → Γ ⊢ `ℕ → Γ ⊢ A → Γ , `ℕ ⊢ A → Γ ⊢ A
  μ_ : ∀ {A} → Γ , A ⊢ A → Γ ⊢ A

_ : ∅ , `ℕ ⇒ `ℕ , `ℕ ⊢ `ℕ
_ = ` Z

_ : ∅ , `ℕ ⇒ `ℕ , `ℕ ⊢ `ℕ ⇒ `ℕ
_ = ` S Z

_ : ∅ , `ℕ ⇒ `ℕ , `ℕ ⊢ `ℕ
_ = ` S Z · ` Z

_ : ∅ , `ℕ ⇒ `ℕ , `ℕ ⊢ `ℕ
_ = ` S Z · (` S Z · ` Z)

_ : ∅ , `ℕ ⇒ `ℕ ⊢ `ℕ ⇒ `ℕ
_ = ƛ (` S Z · (` S Z · ` Z))

_ : ∅ ⊢ (`ℕ ⇒ `ℕ) ⇒ `ℕ ⇒ `ℕ
_ = ƛ ƛ (` S Z · (` S Z · ` Z))

-- Abbreviating de Bruijn indices
lookup : ∀ {n} → Context n → Fin n → Type
lookup {suc n} (Γ , A) FZ = A
lookup {suc n} (Γ , A) (FS i) = lookup Γ i

count : ∀ {n} {Γ : Context n} (i : Fin n) → Γ ∋ lookup Γ i
count {suc n} {Γ , _} FZ = Z
count {suc n} {Γ , _} (FS i) = S (count i)

#_ : ∀ {n} {Γ : Context n} (i : Fin n) → Γ ⊢ lookup Γ i
# i = ` count i

_ : ∅ ⊢ (`ℕ ⇒ `ℕ) ⇒ `ℕ ⇒ `ℕ
_ = ƛ ƛ (# 1 · (# 1 · # 0))

-- Test examples
two : ∀ {n} {Γ : Context n} → Γ ⊢ `ℕ
two = `suc `suc `zero

plus : ∀ {n} {Γ : Context n} → Γ ⊢ `ℕ ⇒ `ℕ ⇒ `ℕ
plus = μ ƛ ƛ (case (# 1) (# 0) (`suc (# 3 · # 0 · # 1)))

2+2 : ∀ {n} {Γ : Context n} → Γ ⊢ `ℕ
2+2 = plus · two · two

Ch : Type → Type
Ch A = (A ⇒ A) ⇒ A ⇒ A

twoᶜ : ∀ {n A} {Γ : Context n} → Γ ⊢ Ch A
twoᶜ = ƛ ƛ (# 1 · (# 1 · # 0))

plusᶜ : ∀ {n A} {Γ : Context n} → Γ ⊢ Ch A ⇒ Ch A ⇒ Ch A
plusᶜ = ƛ ƛ ƛ ƛ (# 3 · # 1 · (# 2 · # 1 · # 0))

sucᶜ : ∀ {n} {Γ : Context n} → Γ ⊢ `ℕ ⇒ `ℕ
sucᶜ = ƛ `suc (# 0)

2+2ᶜ : ∀ {n} {Γ : Context n} → Γ ⊢ `ℕ
2+2ᶜ = plusᶜ · twoᶜ · twoᶜ · sucᶜ · `zero

-- Exercise: mul
-- Z * n = Z
-- (S m) * n = + n (* m n)
mul : ∀ {n} {Γ : Context n} → Γ ⊢ `ℕ ⇒ `ℕ ⇒ `ℕ
mul = μ ƛ ƛ (case (# 1) `zero (plus · # 1 · (# 3 · # 0 · # 1)))

-- Renaming
ext :
  ∀ {m n} {Γ : Context m} {Δ : Context n} →
  (∀ {A} → Γ ∋ A → Δ ∋ A) →
  (∀ {A B} → Γ , B ∋ A → Δ , B ∋ A)
ext ρ Z = Z
ext ρ (S x) = S (ρ x)

rename :
  ∀ {m n} {Γ : Context m} {Δ : Context n} →
  (∀ {A} → Γ ∋ A → Δ ∋ A) →
  (∀ {A} → Γ ⊢ A → Δ ⊢ A)
rename ρ (` x) = ` (ρ x)
rename ρ (ƛ N) = ƛ (rename (ext ρ) N)
rename ρ (L · M) = (rename ρ L) · (rename ρ M)
rename ρ `zero = `zero
rename ρ (`suc M) = `suc (rename ρ M)
rename ρ (case L M N) = case (rename ρ L) (rename ρ M) (rename (ext ρ) N)
rename ρ (μ N) = μ (rename (ext ρ) N)

M₀ : ∅ , `ℕ ⇒ `ℕ ⊢ `ℕ ⇒ `ℕ
M₀ = ƛ (# 1 · (# 1 · # 0))

M₁ : ∅ , `ℕ ⇒ `ℕ , `ℕ ⊢ `ℕ ⇒ `ℕ
M₁ = ƛ (# 2 · (# 2 · # 0))

_ : rename S_ M₀ ≡ M₁
_ = refl

-- Simultaneous substitution
exts :
  ∀ {m n} {Γ : Context m} {Δ : Context n} →
  (∀ {A} → Γ ∋ A → Δ ⊢ A) →
  (∀ {A B} → Γ , B ∋ A → Δ , B ⊢ A)
exts σ Z = ` Z
exts σ (S x) = rename S_ (σ x)

subst :
  ∀ {m n} {Γ : Context m} {Δ : Context n} →
  (∀ {A} → Γ ∋ A → Δ ⊢ A) →
  (∀ {A} → Γ ⊢ A → Δ ⊢ A)
subst σ (` k) = σ k
subst σ (ƛ N) = ƛ (subst (exts σ) N)
subst σ (L · M) = (subst σ L) · (subst σ M)
subst σ `zero = `zero
subst σ (`suc M) = `suc (subst σ M)
subst σ (case L M N) = case (subst σ L) (subst σ M) (subst (exts σ) N)
subst σ (μ N) = μ (subst (exts σ) N)

-- Single substitution
_[_] : ∀ {n A B} {Γ : Context n} → Γ , B ⊢ A → Γ ⊢ B → Γ ⊢ A
_[_] {n} {A} {B} {Γ} N M = subst {suc n} {n} {Γ , B} {Γ} σ {A} N
  where
    σ : ∀ {A} → Γ , B ∋ A → Γ ⊢ A
    σ Z = M
    σ (S x) = ` x

M₂ : ∅ , `ℕ ⇒ `ℕ ⊢ `ℕ ⇒ `ℕ
M₂ = ƛ # 1 · (# 1 · # 0)

M₃ : ∅ ⊢ `ℕ ⇒ `ℕ
M₃ = ƛ `suc # 0

M₄ : ∅ ⊢ `ℕ ⇒ `ℕ
M₄ = ƛ (ƛ `suc # 0) · ((ƛ `suc # 0) · # 0)

_ : M₂ [ M₃ ] ≡ M₄
_ = refl

M₅ : ∅ , `ℕ ⇒ `ℕ , `ℕ ⊢ (`ℕ ⇒ `ℕ) ⇒ `ℕ
M₅ = ƛ # 0 · # 1

M₆ : ∅ , `ℕ ⇒ `ℕ ⊢ `ℕ
M₆ = # 0 · `zero

M₇ : ∅ , `ℕ ⇒ `ℕ ⊢ (`ℕ ⇒ `ℕ) ⇒ `ℕ
M₇ = ƛ (# 0 · (# 1 · `zero))

_ : M₅ [ M₆ ] ≡ M₇
_ = refl

-- Values
data Value : ∀ {n A} {Γ : Context n} → Γ ⊢ A → Set where
  V-ƛ : ∀ {n A B} {Γ : Context n} {N : Γ , A ⊢ B} → Value (ƛ N)
  V-zero : ∀ {n} {Γ : Context n} → Value (`zero {n} {Γ})
  V-suc : ∀ {n} {Γ : Context n} → {V : Γ ⊢ `ℕ} → Value V → Value (`suc V)

-- Reduction
infix 2 _►_

data _►_ {n} {Γ : Context n} : ∀ {A} → (Γ ⊢ A) → (Γ ⊢ A) → Set where
  ξ-·₁ :
    ∀ {A B} {L L′ : Γ ⊢ A ⇒ B} {M : Γ ⊢ A} →
    L ► L′ → L · M ► L′ · M
  ξ-·₂ :
    ∀ {A B} {V : Γ ⊢ A ⇒ B} {M M′ : Γ ⊢ A} →
    Value V → M ► M′ → V · M ► V · M′
  β-ƛ :
    ∀ {A B} {N : Γ , A ⊢ B} {W : Γ ⊢ A} →
    Value W → (ƛ N) · W ► N [ W ]
  ξ-suc :
    {M M′ : Γ ⊢ `ℕ} →
    M ► M′ → `suc M ► `suc M′
  ξ-case :
    ∀ {A} {L L′ : Γ ⊢ `ℕ} {M : Γ ⊢ A} {N : Γ , `ℕ ⊢ A} →
    L ► L′ → case L M N ► case L′ M N
  β-zero :
    ∀ {A} {M : Γ ⊢ A} {N : Γ , `ℕ ⊢ A} →
    case `zero M N ► M
  β-suc :
    ∀ {A} {V : Γ ⊢ `ℕ} {M : Γ ⊢ A} {N : Γ , `ℕ ⊢ A} →
    Value V → case (`suc V) M N ► N [ V ]
  β-μ :
    ∀ {A} {N : Γ , A ⊢ A} →
    μ N ► N [ μ N ]

-- Reflexive and transitive closure
