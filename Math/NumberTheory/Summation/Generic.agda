{-# OPTIONS --without-K --safe #-}

module Math.NumberTheory.Summation.Generic where

-- agda-stdlib
open import Algebra
open import Data.Nat

module MonoidSummation {c e} (M : Monoid c e) where
  open Monoid M renaming (Carrier to A)

  -- Σ< n f = Σₖ₌₀ⁿ⁻¹[f k]
  Σ< : ℕ → (ℕ → A) → A
  Σ< 0       f = ε
  Σ< (suc n) f = Σ< n f ∙ f n

  Σ≤ : ℕ → (ℕ → A) → A
  Σ≤ n f = Σ< (suc n) f

  Σ<range : ℕ → ℕ → (ℕ → A) → A
  Σ<range m n f = Σ< (n ∸ m) (λ o → f (m + o))

  Σ≤range : ℕ → ℕ → (ℕ → A) → A
  Σ≤range m n f = Σ<range m (suc n) f

  syntax Σ< n (λ k → e) = Σ[ k < n ] e
  syntax Σ≤ n (λ k → e) = Σ[ k ≤ n ] e
  syntax Σ<range m n (λ k → e) = Σ[ m ≤ k < n ] e
  syntax Σ≤range m n (λ k → e) = Σ[ m ≤ k ≤ n ] e
