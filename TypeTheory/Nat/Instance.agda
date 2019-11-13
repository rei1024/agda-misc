{-# OPTIONS --without-K --safe #-}

module TypeTheory.Nat.Instance where

-- agda-stdlib
open import Level renaming (zero to lzero; suc to lsuc)
open import Data.Nat using (ℕ; zero; suc)
open import Relation.Binary.PropositionalEquality using (refl)

-- agda-misc
import TypeTheory.Nat.Operations as NatOperations

ℕ-ind : ∀ {l} (P : ℕ → Set l) → P zero → (∀ k → P k → P (suc k)) → ∀ n → P n
ℕ-ind P P-base P-step zero    = P-base
ℕ-ind P P-base P-step (suc n) = P-step n (ℕ-ind P P-base P-step n)

open NatOperations ℕ zero suc ℕ-ind
                   (λ _ _ _ → refl) (λ _ _ _ _ → refl) public
