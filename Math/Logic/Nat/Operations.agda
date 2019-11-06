{-# OPTIONS --without-K --safe #-}

-- agad-stdlib
open import Relation.Binary.PropositionalEquality

module Math.Logic.Nat.Operations
  {a}
  -- | Type of natural number
  (N : Set a)
  -- | Zero
  (zero : N)
  -- | Successor function
  (suc : N → N)
  -- | Induction principle
  (ind : ∀ {p} (P : N → Set p) → P zero → (∀ k → P k → P (suc k)) → ∀ n → P n)
  -- | Computaton rule for `zero`
  (ind-base : ∀ {p} (P : N → Set p) P-base P-step →
    ind P P-base P-step zero ≡ P-base)
  -- | Computaton rule for `suc`
  (ind-step : ∀ {p} (P : N → Set p) P-base P-step n →
    ind P P-base P-step (suc n) ≡ P-step n (ind P P-base P-step n))
  where

-- agda-stdlib
open import Level renaming (zero to lzero; suc to lsuc)
open import Data.Empty
open import Data.Product
open import Data.Bool using (Bool; true; false)
open import Function.Core

private
  variable
    A : Set a

-- recursion
rec : ∀ {l} {A : Set l} → A → (A → A) → N → A
rec {l} {A} z s n = ind (λ _ → A) z (λ k x → s x) n

caseNat : ∀ {l} {A : Set l} (z s : A) → N → A
caseNat {A = A} z s n = ind (λ x → A) z (λ k x → s) n

-- predcessor
pred : N → N
pred n = ind (λ _ → N) zero (λ k x → k) n

-- Arithematic
infixl 6 _+_ _∸_
infixl 7 _*_
infix 4 _≤_ _≰_ _≥_ _≱_ _<_ _≮_ _>_ _≯_
infix 5 _≤ᵇ_

-- Addition
_+_ : N → N → N
m + n = rec n suc m

-- Multiplication
_*_ : N → N → N
m * n = rec zero (λ k → n + k) m

-- Monus
_∸_ : N → N → N
m ∸ n = rec m pred n

-- Order
_≤_ : N → N → Set a
m ≤ n = ∃ λ o → m + o ≡ n

_≰_ : N → N → Set a
m ≰ n = m ≤ n → ⊥

_≥_ : N → N → Set a
m ≥ n = n ≤ m

_≱_ : N → N → Set a
m ≱ n = m ≥ n → ⊥

_<_ : N → N → Set a
m < n = suc m ≤ n

_≮_ : N → N → Set a
m ≮ n = m < n → ⊥

_>_ : N → N → Set a
m > n = n < m

_≯_ : N → N → Set a
m ≯ n = m > n → ⊥

-- Order (Bool)
_≤ᵇ_ : N → N → Bool
m ≤ᵇ n = caseNat true false (m ∸ n)

-- induction
ind2 : ∀ {p} (P : N → N → Set p) →
  P zero zero →
  (∀ m n → P m n → P m (suc n)) →
  (∀ m n → P m n → P (suc m) n) →
  ∀ m n → P m n
ind2 P Pzz Pmn→Pms Pmn→Psn m n = ind
  (λ o → P o n)
  (ind (λ p → P zero p) Pzz (λ k Pzk → Pmn→Pms zero k Pzk) n)
  (λ k Pkn → ind (λ r → P (suc k) r) (P[k,0] (suc k))
    (λ k₁ P[1+k,k₁] → Pmn→Pms (suc k) k₁ P[1+k,k₁]) n)
  m
  where
  P[k,0] : ∀ k → P k zero
  P[k,0] = λ k → ind (λ x → P x zero) Pzz (λ k₂ → Pmn→Psn k₂ zero) k

-- Constant
one : N
one = suc zero
