{-# OPTIONS --without-K --safe #-}

-- agad-stdlib
open import Relation.Binary.PropositionalEquality

module Math.Logic.Nat.Properties
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
open import Data.Unit using (⊤ ; tt)
open import Data.Product
open import Function.Core
open import Relation.Nullary
import Relation.Nullary.Decidable as NDec

-- agda-misc
open import Math.Logic.Nat.Operations N zero suc ind ind-base ind-step

open ≡-Reasoning

private
  variable
    A : Set a

rec-base : ∀ {A : Set a} (z : A) s → rec z s zero ≡ z
rec-base {A} z s = ind-base (λ _ → A) z λ k x → s x

rec-step : ∀ {A : Set a} (z : A) s n → rec z s (suc n) ≡ s (rec z s n)
rec-step {A} z s n = ind-step (λ _ → A) z (λ k x → s x) n

---------------------------------------------------------------------------
pred-zero : pred zero ≡ zero
pred-zero = ind-base (λ _ → N) zero (λ k x → k)

pred-suc : ∀ n → pred (suc n) ≡ n
pred-suc n = ind-step (λ _ → N) zero (λ k x → k) n

suc-injective : ∀ {m n} → suc m ≡ suc n → m ≡ n
suc-injective {m} {n} 1+m≡1+n = begin
  m            ≡⟨ sym $ pred-suc m ⟩
  pred (suc m) ≡⟨ cong pred 1+m≡1+n ⟩
  pred (suc n) ≡⟨ pred-suc n ⟩
  n            ∎

caseNat : ∀ {l} {A : Set l} (z s : A) → N → A
caseNat {A = A} z s n = ind (λ x → A) z (λ k x → s) n

caseNat-base : ∀ {l} {A : Set l} (z s : A) → caseNat z s zero ≡ z
caseNat-base z s = ind-base (λ x → _) z λ k x → s

caseNat-step : ∀ {l} {A : Set l} (z s : A) n → caseNat z s (suc n) ≡ s
caseNat-step z s n = ind-step (λ x → _) z (λ k x → s) n

NotZero : ∀ n → Set
NotZero n = caseNat ⊥ ⊤ n

NotZero[zero]≡⊥ : NotZero zero ≡ ⊥
NotZero[zero]≡⊥ = caseNat-base ⊥ ⊤

NotZero[suc[n]]≡⊤ : ∀ n → NotZero (suc n) ≡ ⊤
NotZero[suc[n]]≡⊤ n = caseNat-step ⊥ ⊤ n

private
  transport : ∀ {a} {A B : Set a} → A ≡ B → A → B
  transport eq = subst id eq

NotZero[suc[n]] : ∀ (n : N) → NotZero (suc n)
NotZero[suc[n]] n = transport (sym $ NotZero[suc[n]]≡⊤ n) tt

s≢z : ∀ (n : N) → suc n ≢ zero
s≢z n eq = transport NotZero[zero]≡⊥ $ subst NotZero eq (NotZero[suc[n]] n)

z≢s : ∀ (n : N) → zero ≢ suc n
z≢s n eq = s≢z n (sym eq)

1+n≢n : ∀ n → suc n ≢ n
1+n≢n n = ind (λ x → suc x ≢ x) (s≢z zero)
  (λ k 1+k≢k 1+[1+k]≡1+k → 1+k≢k (suc-injective 1+[1+k]≡1+k)) n

-- Order

-- ≤-antisym : ∀ m n → m ≤ n → n ≤ m → m ≡ n
-- ≤-antisym m n = {!   !}

-- n≮0 : ∀ n → n ≮ zero
-- n < zero
-- 1+n ≤ zero
-- zero ≤ 1+n
-- zero≡1+n
-- ⊥

-- decidability
private
  Dec-elim : ∀ {a p} {A : Set a} {P : Dec A → Set p} → (∀ p → P (yes p)) → (∀ p → P (no p)) → ∀ d → P d
  Dec-elim x y (yes p) = x p
  Dec-elim x y (no ¬p) = y ¬p

zero? : ∀ (n : N) → Dec (n ≡ zero)
zero? n = ind (λ x → Dec (x ≡ zero)) (yes refl) (λ k x → no (s≢z k)) n
{-
suc? : ∀ (m n : N) → Dec (m ≡ n) → Dec (m ≡ suc n)
suc? m n d = ind (λ x → Dec (x ≡ suc n)) (NDec.map′ sym sym $ zero? (suc n))
  (λ k x → Dec-elim (λ k≡1+n → no (λ 1+k≡1+n → 1+n≢n k (trans 1+k≡1+n (sym k≡1+n))))

  (λ p → yes (cong suc {!   !})) x) m

_≟_ : ∀ (m n : N) → Dec (m ≡ n)
_≟_ m n = ind (λ x → Dec (m ≡ x)) (zero? m) {!   !} n
-}

-- Properties of _+_
+-identityˡ : ∀ n → zero + n ≡ n
+-identityˡ n = rec-base n suc

suc-+ : ∀ m n → suc m + n ≡ suc (m + n)
suc-+ m n = rec-step n suc m

+-identityʳ : ∀ n → n + zero ≡ n
+-identityʳ n₀ = ind (λ n → n + zero ≡ n) (+-identityˡ zero) step n₀
  where
  step : ∀ k → k + zero ≡ k → suc k + zero ≡ suc k
  step k k+zero≡k = begin
    suc k + zero   ≡⟨ suc-+ k zero ⟩
    suc (k + zero) ≡⟨ cong suc k+zero≡k ⟩
    suc k          ∎

+-assoc : ∀ m n o → (m + n) + o ≡ m + (n + o)
+-assoc m₀ n o = ind (λ m → (m + n) + o ≡ m + (n + o)) base step m₀
  where
  base : (zero + n) + o ≡ zero + (n + o)
  base = begin
    (zero + n) + o ≡⟨ cong (_+ o) $ +-identityˡ n ⟩
    n + o          ≡⟨ sym $ +-identityˡ (n + o) ⟩
    zero + (n + o) ∎

  step : ∀ k → (k + n) + o ≡ k + (n + o) → (suc k + n) + o ≡ suc k + (n + o)
  step k [k+n]+o≡k+[n+o] = begin
    (suc k + n) + o   ≡⟨ cong (_+ o) $ suc-+ k n ⟩
    suc (k + n) + o   ≡⟨ suc-+ (k + n) o ⟩
    suc ((k + n) + o) ≡⟨ cong suc [k+n]+o≡k+[n+o] ⟩
    suc (k + (n + o)) ≡⟨ sym $ suc-+ k (n + o) ⟩
    suc k + (n + o)   ∎

+-suc : ∀ m n → m + suc n ≡ suc m + n
+-suc m₀ n = ind (λ m → m + suc n ≡ suc m + n)
   (begin
    zero + suc n   ≡⟨ +-identityˡ (suc n) ⟩
    suc n          ≡⟨ cong suc (sym $ +-identityˡ n) ⟩
    suc (zero + n) ≡⟨ sym $ suc-+ zero n ⟩
    suc zero + n   ∎
    )
  (λ m m+[1+n]≡[1+m]+n → begin
    suc m + suc n   ≡⟨ suc-+ m (suc n) ⟩
    suc (m + suc n) ≡⟨ cong suc m+[1+n]≡[1+m]+n ⟩
    suc (suc m + n) ≡⟨ sym $ suc-+ (suc m) n ⟩
    suc (suc m) + n ∎
    )
  m₀

+-comm : ∀ m n → m + n ≡ n + m
+-comm m₀ n = ind (λ m → m + n ≡ n + m)
  (begin
    zero + n ≡⟨ +-identityˡ n ⟩
    n        ≡⟨ sym $ +-identityʳ n ⟩
    n + zero ∎
    )
  (λ m m+n≡n+m → begin
    suc m + n   ≡⟨ suc-+ m n ⟩
    suc (m + n) ≡⟨ cong suc m+n≡n+m ⟩
    suc (n + m) ≡⟨ sym $ suc-+ n m ⟩
    suc n + m   ≡⟨ sym $ +-suc n m ⟩
    n + suc m   ∎
    )
  m₀
