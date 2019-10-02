{-# OPTIONS --without-K --safe #-}

module Math.NumberTheory.Summation.Nat.Properties where

-- agda-stdlib
open import Data.Nat
open import Data.Nat.Properties
open import Relation.Binary.PropositionalEquality
open import Function.Core

-- agda-misc
open import Math.NumberTheory.Summation.Generic
open import Math.NumberTheory.Summation.Generic.Properties

open MonoidSummation +-0-monoid

open SemiringSummationProperties *-+-semiring public
  renaming
  ( Σ<[f,1]≈f[0] to Σ<[f,1]≡f[0]
  ; Σ≤[f,0]≈f[0] to Σ≤[f,0]≡f[0]
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
