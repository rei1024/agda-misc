open import TypeTheory.Nat.AnotherMono.Structure

module TypeTheory.Nat.AnotherMono.Properties (nat : Nat) where

open import Level renaming (zero to lzero; suc to lsuc)
open import Data.Empty using (⊥)
open import Data.Product using (Σ; _×_; _,_)
open import Data.Sum
open import Relation.Binary using (Rel)
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary using (¬_)
open import Function.Base

open Nat nat

+-identityˡ : ∀ n → zero + n ≡ n
+-identityˡ n = rec-zero _ _

+-suc : ∀ m n → suc m + n ≡ suc (m + n)
+-suc m n = rec-suc _ _ _

+-identityʳ : ∀ n → n + zero ≡ n
+-identityʳ n = ind (λ k → k + zero ≡ k) (+-identityˡ zero)
                    (λ k k+z≡k → trans (+-suc k zero) (cong suc k+z≡k) )
                    n

1N+n≡sn : ∀ n → 1N + n ≡ suc n
1N+n≡sn n = begin
  suc zero + n   ≡⟨ +-suc zero n ⟩
  suc (zero + n) ≡⟨ cong suc (+-identityˡ n) ⟩
  suc n          ∎
  where open ≡-Reasoning

+-suc-comm : ∀ m n → suc m + n ≡ m + suc n
+-suc-comm m n =
  ind
    (λ o → suc o + n ≡ o + suc n)
    (begin
      suc zero + n ≡⟨ 1N+n≡sn n ⟩
      suc n        ≡⟨ sym $ +-identityˡ (suc n) ⟩
      zero + suc n ∎)
    (λ o so+n≡o+sn → begin
      suc (suc o) + n ≡⟨ +-suc (suc o) n ⟩
      suc (suc o + n) ≡⟨ cong suc so+n≡o+sn ⟩
      suc (o + suc n) ≡⟨ sym $ +-suc o (suc n) ⟩
      suc o + suc n   ∎)
    m
  where open ≡-Reasoning

z≤n : ∀ n → zero ≤ n
z≤n n = n , {!   !}

≤-step : ∀ {m n} → m ≤ n → m ≤ suc n
≤-step {m} {n} (o , m+o≡n) = suc o , {!   !}
  where open ≡-Reasoning

≤-refl : ∀ {n} → n ≤ n
≤-refl {n} = zero , {!   !}

s≤s : ∀ {m n} → m ≤ n → suc m ≤ suc n
s≤s {m} {n} (o , m+o≡n) = o , {!   !}

s<s : ∀ {m n} → m < n → suc m < suc n
s<s = s≤s

z<s : ∀ n → zero < suc n
z<s n = s≤s (z≤n n)

n<sn : ∀ n → n < suc n
n<sn n = ≤-refl {suc n}

≤⇒<∨≡ : ∀ {m n} → m ≤ n → m < n ⊎ m ≡ n
≤⇒<∨≡ {m} {n} (o , o+m≡n) = {!   !}

data Order (m n : N) : Set where
  less    : (m<n : m < n) → Order m n
  equal   : (m≡n : m ≡ n) → Order m n
  greater : (m>n : m > n) → Order m n

order? : ∀ m n → Order m n
order? m₀ n₀ = ind (λ m → Order m n₀) order?-zero order?-suc m₀
  where
  order?-zero : Order zero n₀
  order?-zero = ind (Order zero) (equal refl) (λ _ _ → less (z<s _)) n₀

  order?-suc : ∀ m → Order m n₀ → Order (suc m) n₀
  order?-suc m (less sm≤n) with ≤⇒<∨≡ sm≤n
  ... | inj₁ sm<n = less sm<n
  ... | inj₂ sm≡n = equal sm≡n
  order?-suc m (equal refl)  = greater (n<sn _)
  order?-suc m (greater m>n) = greater (≤-step m>n)

-- indΔ :
module _ (P : N → N → Set) where
  indΔ< : (∀ n → P zero (suc n)) →
          (∀ m n → P m n → P (suc m) (suc n)) →
          ∀ m o → P m (o + suc m)
  indΔ< Pzs Pss m o = ind
    (λ k → P k (o + suc k))
    (subst (P zero) {!   !} (Pzs o)) {!   !} {!   !}

  indΔ : P zero zero →
         (∀ n → P zero (suc n)) →
         (∀ m → P (suc m) zero) →
         (∀ m n → P m n → P (suc m) (suc n)) →
         ∀ m n → P m n
  indΔ Pzz Pzs Psz Pss m n with order? m n
  ... | less    (o , o+sm≡n) = subst (P m) o+sm≡n $′ indΔ< Pzs Pss m o
  ... | equal   m≡n = {!   !}
  ... | greater m>n = {!   !}
