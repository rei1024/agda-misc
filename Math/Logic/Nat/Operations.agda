{-# OPTIONS --without-K --safe #-}

-- agad-stdlib
open import Relation.Binary.PropositionalEquality

module Math.Logic.Nat.Operations
  {a}
  (N : Set a)
  (zero : N)
  (suc : N → N)
  (ind : ∀ {p} (P : N → Set p) → P zero → (∀ k → P k → P (suc k)) → ∀ n → P n)
  (ind-base : ∀ {p} (P : N → Set p) P-base P-step →
    ind P P-base P-step zero ≡ P-base)
  (ind-step : ∀ {p} (P : N → Set p) P-base P-step n →
    ind P P-base P-step (suc n) ≡ P-step n (ind P P-base P-step n))
  where

-- agda-stdlib
open import Level renaming (zero to lzero; suc to lsuc)
open import Data.Empty
open import Data.Product
open import Function.Core

private
  variable
    A : Set a

rec : ∀ {l} {A : Set l} → A → (A → A) → N → A
rec {l} {A} z s n = ind (λ _ → A) z (λ k x → s x) n

pred : N → N
pred n = ind (λ _ → N) zero (λ k x → k) n

-- Arithematic
infixl 6 _+_ _*_
_+_ : N → N → N
m + n = rec n suc m

_*_ : N → N → N
m * n = rec zero (λ k → n + k) m

-- Order
_≤_ : N → N → Set a
m ≤ n = ∃ λ o → m ≡ n + o

_<_ : N → N → Set a
m < n = suc m ≤ n

_≮_ : N → N → Set a
m ≮ n = m < n → ⊥
{-
ind-< : ∀ {p} (P : N → Set p) →
  (∀ l → (∀ k → k < l → P k) → P l) →
  ∀ n → P n
ind-< P P-acc n = ind P (P-acc zero {!   !}) {!   !} n

ind2 : ∀ {p} (P : N → N → Set p) →
    P zero zero →
    (∀ n → P zero (suc n)) →
    (∀ m → P (suc m) zero) →
    (∀ m n → P m n → P (suc m) (suc n)) →
    ∀ m n → P m n
ind2 P P-zz P-zs P-sz P-ss m₀ n₀ = ind
  (λ m → P m n₀)
  (ind (λ n → P zero n) P-zz (λ k P[0,k] → P-zs k) n₀)
  (λ k P[k,n₀] → ind (λ n → P (suc k) n) (P-sz k) (λ o P[1+k,o] → P-ss k o {! ? !}) n₀)
  m₀
-}
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

ind2-zz : ∀ {p} (P : N → N → Set p) Pzz Pmn→Pms Pmn→Psn →
  ind2 P Pzz Pmn→Pms Pmn→Psn zero zero ≡ Pzz
ind2-zz P Pzz Pmn→Pms Pmn→Psn = begin
  ind2 P Pzz Pmn→Pms Pmn→Psn zero zero
    ≡⟨⟩
  ind
      (λ o → P o zero)
      (ind (λ p → P zero p) Pzz (λ k Pzk → Pmn→Pms zero k Pzk) zero)
      (λ k Pkn → ind (λ r → P (suc k) r) (( λ k → ind (λ x → P x zero) Pzz (λ k₂ Pk₂zero → Pmn→Psn k₂ zero Pk₂zero) k) (suc k))
        (λ k₁ P[1+k,k₁] → Pmn→Pms (suc k) k₁ P[1+k,k₁]) zero)
      zero
    ≡⟨ ind-base _ _ _ ⟩
  ind (λ p → P zero p) Pzz (Pmn→Pms zero) zero
    ≡⟨ ind-base _ _ _ ⟩
  Pzz
    ∎
  where open ≡-Reasoning

  {-
  trans (ind-base (λ x → P x zero) {! (ind (P zero) Pzz (Pmn→Pms zero) zero)  Pzz  !} {! λ k → Pmn→Psn k zero  !})
  (ind-base (λ x → P zero x) Pzz λ k Pzk → Pmn→Pms zero k Pzk)
  -}
{-
ind2-P-ss : ind2 P P-zz P-zs P-sz P-ss (suc m) (suc n) ≡
            P-ss m n (ind2 P P-zz P-zs P-sz P-ss m n)
-}
