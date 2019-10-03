{-# OPTIONS --without-K --safe #-}

module Math.NumberTheory.Summation.Nat.Properties where

-- agda-stdlib
open import Algebra
import Algebra.Operations.CommutativeMonoid as CommutativeMonoidOperations
open import Data.Nat
open import Data.Nat.Properties
open import Data.Nat.Solver
open import Relation.Binary.PropositionalEquality
open import Function.Core

-- agda-misc
open import Math.NumberTheory.Summation.Generic
open import Math.NumberTheory.Summation.Generic.Properties
import Math.NumberTheory.Summation.Nat.Properties.Lemma as Lemma

open MonoidSummation (Semiring.+-monoid *-+-semiring)
open CommutativeMonoidOperations (Semiring.+-commutativeMonoid *-+-semiring)

-- TODO rename _≈_ to _≡_
open SemiringSummationProperties *-+-semiring public
  renaming
  ( Σ<[f,1]≈f[0] to Σ<[f,1]≡f[0]
  ; Σ≤[f,0]≈f[0] to Σ≤[f,0]≡f[0]
  ; n≤m⇒Σ<range[f,m,n]≈0 to n≤m⇒Σ<range[f,m,n]≡0
  ; Σ<range[f,n,n]≈0 to Σ<range[f,n,n]≡0
  ; Σ<range[f,m,m+n+o]≈Σ<range[f,m,m+n]+Σ<range[m+n,m+n+o] to
      Σ<range[f,m,m+n+o]≡Σ<range[f,m,m+n]+Σ<range[m+n,m+n+o]
  ; Σ<range[f,m,n]≈Σ<range[f,m,o]+Σ<range[f,o,n] to
      Σ<range[f,m,n]≡Σ<range[f,m,o]+Σ<range[f,o,n]
  ; Σ<range[f,m,n]≈Σ<range[i→f[i∸o],o+m,o+n] to
      Σ<range[f,m,n]≡Σ<range[i→f[i∸o],o+m,o+n]
  ; Σ<-const to Σ<-const-×
  ; Σ≤-const to Σ≤-const-×
  ; Σ<range-const to Σ<range-const-×
  ; Σ≤range-const to Σ≤range-const-×
  )

-- TODO move somewhere
private
  m×n≡m*n : ∀ m n → m × n ≡ m * n
  m×n≡m*n zero    n = refl
  m×n≡m*n (suc m) n = cong (n +_) $ m×n≡m*n m n

Σ<-const : ∀ m n → Σ< (λ _ → m) n ≡ n * m
Σ<-const m n = begin-equality
  Σ< (λ _ → m) n ≡⟨ Σ<-const-× m n ⟩
  n × m          ≡⟨ m×n≡m*n n m ⟩
  n * m          ∎
  where open ≤-Reasoning

Σ≤-const : ∀ m n → Σ≤ (λ _ → m) n ≡ suc n * m
Σ≤-const m n = Σ<-const m (suc n)

Σ<range-const : ∀ x m n → Σ<range (const x) m n ≡ (n ∸ m) * x
Σ<range-const x m n = trans (Σ<range-const-× x m n) (m×n≡m*n (n ∸ m) x)

Σ≤range-const : ∀ x m n → Σ≤range (const x) m n ≡ (suc n ∸ m) * x
Σ≤range-const x m n = Σ<range-const x m (suc n)

2*Σ≤[id,n]≡n*[1+n] : ∀ n → 2 * Σ≤ id n ≡ n * (suc n)
2*Σ≤[id,n]≡n*[1+n] zero    = refl
2*Σ≤[id,n]≡n*[1+n] (suc n) = begin-equality
  2 * Σ≤ id (suc n)       ≡⟨⟩
  2 * (Σ≤ id n + suc n)   ≡⟨ *-distribˡ-+ 2 (Σ≤ id n) (suc n) ⟩
  2 * Σ≤ id n + 2 * suc n ≡⟨ cong (_+ 2 * suc n) $ 2*Σ≤[id,n]≡n*[1+n] n ⟩
  n * suc n + 2 * suc n   ≡⟨ sym $ *-distribʳ-+ (suc n) n 2 ⟩
  (n + 2) * suc n         ≡⟨ *-comm (n + 2) (suc n) ⟩
  suc n * (n + 2)         ≡⟨ cong (suc n *_) $ +-comm n 2 ⟩
  suc n * suc (suc n)     ∎
  where open ≤-Reasoning

6*Σ≤[^2,n]≡n*[1+n]*[1+2*n] : ∀ n → 6 * Σ≤ (_^ 2) n ≡ n * (1 + n) * (1 + 2 * n)
6*Σ≤[^2,n]≡n*[1+n]*[1+2*n] 0       = refl
6*Σ≤[^2,n]≡n*[1+n]*[1+2*n] (suc n) = begin-equality
  6 * Σ≤ (_^ 2) (suc n)                          ≡⟨⟩
  6 * (Σ≤ (_^ 2) n + suc n ^ 2)                  ≡⟨ *-distribˡ-+ 6 (Σ≤ (_^ 2) n) (suc n ^ 2) ⟩
  6 *  Σ≤ (_^ 2) n + 6 * (suc n ^ 2)             ≡⟨ cong (_+ 6 * (suc n ^ 2)) $ 6*Σ≤[^2,n]≡n*[1+n]*[1+2*n] n ⟩
   n * (1 + n) * (1 + 2 * n) + 6 * ((1 + n) ^ 2) ≡⟨ Lemma.lemma₁ n ⟩
  (1 + n) * (2 + n) * (1 + 2 * (1 + n))          ∎
  where open ≤-Reasoning
