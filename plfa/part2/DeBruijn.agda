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

count : ∀ {n} → {Γ : Context n} → (i : Fin n) → Γ ∋ lookup Γ i
count {suc n} {Γ , _} FZ = Z
count {suc n} {Γ , _} (FS i) = S (count i)

#_ : ∀ {n} → {Γ : Context n} → (i : Fin n) → Γ ⊢ lookup Γ i
# i = ` count i

_ : ∅ ⊢ (`ℕ ⇒ `ℕ) ⇒ `ℕ ⇒ `ℕ
_ = ƛ ƛ (# 1 · (# 1 · # 0))

-- Test examples
