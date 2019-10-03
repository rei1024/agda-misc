{-# OPTIONS --without-K --safe #-}

module Math.NumberTheory.Summation.Generic where

-- agda-stdlib
open import Algebra
open import Data.Nat

module MonoidSummation {c e} (M : Monoid c e) where
  open Monoid M renaming (Carrier to A)

  -- Σ< f n = Σₖ₌₀ⁿ⁻¹[f k]
  Σ< : (ℕ → A) → ℕ → A
  Σ< f 0       = ε
  Σ< f (suc n) = Σ< f n ∙ f n

  Σ≤ : (ℕ → A) → ℕ → A
  Σ≤ f n = Σ< f (suc n)

  Σ<range : (ℕ → A) → ℕ → ℕ → A
  Σ<range f m n = Σ< (λ o → f (m + o)) (n ∸ m)

  Σ≤range : (ℕ → A) → ℕ → ℕ → A
  Σ≤range f m n = Σ<range f m (suc n)

  syntax Σ< (λ k → e) n = Σ[ k < n ] e
  syntax Σ≤ (λ k → e) n = Σ[ k ≤ n ] e
  syntax Σ<range (λ k → e) m n = Σ[ m ≤ k < n ] e
  syntax Σ≤range (λ k → e) m n = Σ[ m ≤ k ≤ n ] e
