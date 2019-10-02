{-# OPTIONS --without-K --safe #-}

module Math.NumberTheory.Summation.Generic.Base where

-- agda-stdlib
open import Algebra
open import Data.Nat

module MonoidSummationBase {c e} (M : Monoid c e) where
  open Monoid M renaming (Carrier to A)

  -- Σ< f n = Σₖ₌₀ⁿ⁻¹[f k]
  Σ< : (ℕ → A) → ℕ → A
  Σ< f 0       = ε
  Σ< f (suc n) = f n ∙ Σ< f n

  Σ≤ : (ℕ → A) → ℕ → A
  Σ≤ f n = Σ< f (suc n)

  Σrange : (ℕ → A) → ℕ → ℕ → A
  Σrange f m n = Σ≤ (λ o → f (m + o)) (n ∸ m)

  syntax Σ< (λ k → e) n = Σ[ k < n ] e
  syntax Σ≤ (λ k → e) n = Σ[ k ≤ n ] e
  syntax Σrange (λ k → e) m n = Σ[ m ≤ k ≤ n ] e
