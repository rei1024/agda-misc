{-# OPTIONS --without-K --safe #-}

module Math.Logic.Nat.Instance where

-- agda-stdlib
open import Level renaming (zero to lzero; suc to lsuc)
open import Data.Nat
open import Relation.Binary.PropositionalEquality

-- agda-misc
import Math.Logic.Nat.Operations as NatOperations

ℕ-ind : ∀ {l} (P : ℕ → Set l) → P zero → (∀ k → P k → P (suc k)) → ∀ n → P n
ℕ-ind P P-base P-step zero    = P-base
ℕ-ind P P-base P-step (suc n) = P-step n (ℕ-ind P P-base P-step n)

open NatOperations ℕ zero suc ℕ-ind
  (λ P P-base P-step → refl) (λ P P-base P-step n → refl) public
