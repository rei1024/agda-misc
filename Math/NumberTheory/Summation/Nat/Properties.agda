{-# OPTIONS --without-K --safe #-}

module Math.NumberTheory.Summation.Nat.Properties where

-- agda-stdlib
open import Data.Nat
open import Data.Nat.Properties
open import Data.Nat.Solver
open import Relation.Binary.PropositionalEquality
open import Function.Core

-- agda-misc
open import Math.NumberTheory.Summation.Generic
open import Math.NumberTheory.Summation.Generic.Properties
import Math.NumberTheory.Summation.Nat.Properties.Lemma as Lemma

open MonoidSummation +-0-monoid

open SemiringSummationProperties *-+-semiring public
  renaming
  ( Σ<[f,1]≈f[0] to Σ<[f,1]≡f[0]
  ; Σ≤[f,0]≈f[0] to Σ≤[f,0]≡f[0]
  ; Σ<range[f,n,n]≈0 to Σ<range[f,n,n]≡0
  ; Σ<-const to Σ<-const-×
  ; Σ≤-const to Σ≤-const-×
  )

Σ<-const : ∀ m n → Σ< (λ _ → m) n ≡ m * n
Σ<-const m zero    = sym (*-zeroʳ m)
Σ<-const m (suc n) = begin-equality
  m + Σ< (λ _ → m) n ≡⟨ cong (m +_) $ Σ<-const m n ⟩
  m + (m * n)        ≡⟨ sym $ *-suc m n ⟩
  m * suc n          ∎
  where open ≤-Reasoning

Σ≤-const : ∀ m n → Σ≤ (λ _ → m) n ≡ m * suc n
Σ≤-const m n = Σ<-const m (suc n)

2*Σ≤[id,n]≡n*[1+n] : ∀ n → 2 * Σ≤ id n ≡ n * (suc n)
2*Σ≤[id,n]≡n*[1+n] zero    = refl
2*Σ≤[id,n]≡n*[1+n] (suc n) = begin-equality
  2 * Σ≤ id (suc n)       ≡⟨⟩
  2 * (suc n + Σ≤ id n)   ≡⟨ *-distribˡ-+ 2 (suc n) (Σ≤ id n) ⟩
  2 * suc n + 2 * Σ≤ id n ≡⟨ cong (2 * suc n +_) $ 2*Σ≤[id,n]≡n*[1+n] n ⟩
  2 * suc n + n * suc n   ≡⟨ sym $ *-distribʳ-+ (suc n) 2 n ⟩
  (2 + n) * suc n         ≡⟨ *-comm (2 + n) (suc n) ⟩
  suc n * suc (suc n)     ∎
  where open ≤-Reasoning

6*Σ≤[^2,n]≡n*[1+n]*[1+2*n] : ∀ n → 6 * Σ≤ (_^ 2) n ≡ n * (1 + n) * (1 + 2 * n)
6*Σ≤[^2,n]≡n*[1+n]*[1+2*n] 0       = refl
6*Σ≤[^2,n]≡n*[1+n]*[1+2*n] (suc n) = begin-equality
  6 * Σ≤ (_^ 2) (suc n)                         ≡⟨⟩
  6 * ((suc n ^ 2) + Σ≤ (_^ 2) n)               ≡⟨ *-distribˡ-+ 6 (suc n ^ 2) (Σ≤ (_^ 2) n) ⟩
  6 * (suc n ^ 2) + 6 * Σ≤ (_^ 2) n             ≡⟨ cong (6 * (suc n ^ 2) +_) $ 6*Σ≤[^2,n]≡n*[1+n]*[1+2*n] n ⟩
  6 * ((1 + n) ^ 2) + n * (1 + n) * (1 + 2 * n) ≡⟨ Lemma.lemma₁ n ⟩
  (1 + n) * (2 + n) * (1 + 2 * (1 + n))         ∎
  where open ≤-Reasoning
