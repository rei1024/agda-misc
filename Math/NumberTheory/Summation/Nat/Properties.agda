{-# OPTIONS --without-K --safe #-}

module Math.NumberTheory.Summation.Nat.Properties where

-- agda-stdlib
open import Algebra
import Algebra.Operations.CommutativeMonoid as CommutativeMonoidOperations
open import Data.Nat
open import Data.Nat.Properties
open import Data.Nat.Solver
open import Relation.Binary.PropositionalEquality
open import Function.Base

-- agda-misc
open import Math.NumberTheory.Summation.Generic
open import Math.NumberTheory.Summation.Generic.Properties
import Math.NumberTheory.Summation.Nat.Properties.Lemma as Lemma

-- DO NOT change this line
open MonoidSummation (Semiring.+-monoid *-+-semiring)
open CommutativeMonoidOperations (Semiring.+-commutativeMonoid *-+-semiring)

-- TODO? rename _≈_ to _≡_ this is tedious
open SemiringSummationProperties *-+-semiring public
  renaming
  ( Σ<-const to Σ<-const-×
  ; Σ≤-const to Σ≤-const-×
  ; Σ<range-const to Σ<range-const-×
  ; Σ≤range-const to Σ≤range-const-×
  )

-- TODO move somewhere
private
  m×n≡m*n : ∀ m n → m × n ≡ m * n
  m×n≡m*n zero    n = refl
  m×n≡m*n (suc m) n = cong (n +_) $ m×n≡m*n m n

Σ<-const : ∀ m n → Σ< m (λ _ → n) ≡ m * n
Σ<-const m n = begin-equality
  Σ< m (λ _ → n) ≡⟨ Σ<-const-× m n ⟩
  m × n          ≡⟨ m×n≡m*n m n ⟩
  m * n          ∎
  where open ≤-Reasoning

Σ≤-const : ∀ m n → Σ≤ m (λ _ → n) ≡ suc m * n
Σ≤-const m n = Σ<-const (suc m) n

Σ<range-const : ∀ m n x → Σ<range m n (const x) ≡ (n ∸ m) * x
Σ<range-const m n x = trans (Σ<range-const-× m n x) (m×n≡m*n (n ∸ m) x)

Σ≤range-const : ∀ m n x → Σ≤range m n (const x) ≡ (suc n ∸ m) * x
Σ≤range-const m n x = Σ<range-const m (suc n) x

2*Σ≤[n,id]≡n*[1+n] : ∀ n → 2 * Σ≤ n id ≡ n * (suc n)
2*Σ≤[n,id]≡n*[1+n] zero    = refl
2*Σ≤[n,id]≡n*[1+n] (suc n) = begin-equality
  2 * Σ≤ (suc n) id       ≡⟨⟩
  2 * (Σ≤ n id + suc n)   ≡⟨ *-distribˡ-+ 2 (Σ≤ n id) (suc n) ⟩
  2 * Σ≤ n id + 2 * suc n ≡⟨ cong (_+ 2 * suc n) $ 2*Σ≤[n,id]≡n*[1+n] n ⟩
  n * suc n + 2 * suc n   ≡⟨ sym $ *-distribʳ-+ (suc n) n 2 ⟩
  (n + 2) * suc n         ≡⟨ *-comm (n + 2) (suc n) ⟩
  suc n * (n + 2)         ≡⟨ cong (suc n *_) $ +-comm n 2 ⟩
  suc n * suc (suc n)     ∎
  where open ≤-Reasoning

6*Σ≤[n,^2]≡n*[1+n]*[1+2*n] : ∀ n → 6 * Σ≤ n (_^ 2) ≡ n * (1 + n) * (1 + 2 * n)
6*Σ≤[n,^2]≡n*[1+n]*[1+2*n] 0       = refl
6*Σ≤[n,^2]≡n*[1+n]*[1+2*n] (suc n) = begin-equality
  6 * Σ≤ (suc n) (_^ 2)                          ≡⟨⟩
  6 * (Σ≤ n (_^ 2) + suc n ^ 2)                  ≡⟨ *-distribˡ-+ 6 (Σ≤ n (_^ 2)) (suc n ^ 2) ⟩
  6 *  Σ≤ n (_^ 2) + 6 * (suc n ^ 2)             ≡⟨ cong (_+ 6 * (suc n ^ 2)) $ 6*Σ≤[n,^2]≡n*[1+n]*[1+2*n] n ⟩
   n * (1 + n) * (1 + 2 * n) + 6 * ((1 + n) ^ 2) ≡⟨ Lemma.lemma₁ n ⟩
  (1 + n) * (2 + n) * (1 + 2 * (1 + n))          ∎
  where open ≤-Reasoning

-- Arithmetic sequence
{-
2*Σ<[n,i→d+a*i]≡??? : ∀ n d a → 2 * Σ< n (λ i → d + a * i) ≡ n * (2 * d + a * suc n)
2*Σ<[n,i→d+a*i]≡??? n d a = begin-equality
  2 * Σ< n (λ i → d + a * i)
    ≡⟨ {!   !} ⟩
  2 * (Σ< n (λ _ → d) + Σ< n (λ i → a * i))

  2 * (n * d + a * Σ< n id)
  2 * (n * d) + 2 * (a * Σ< n id)
  2 * n * d + a * (2 * Σ< n id)
  2 * n * d + a * (n * suc n)
  n * (2 * d + a * suc n)
    ∎
  where oepn ≤-Reasoning
-}
