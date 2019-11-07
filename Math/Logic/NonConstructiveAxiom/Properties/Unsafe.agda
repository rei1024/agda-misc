{-# OPTIONS --without-K #-}

module Math.Logic.NonConstructiveAxiom.Properties.Unsafe where

-- agda-stdlib
open import Data.Nat
open import Data.Product
open import Data.Sum
open import Relation.Nullary

-- agda-misc
open import Math.Logic.NonConstructiveAxiom

{-# TERMINATING #-}
mp-ℕ : ∀ {p} → MP ℕ p
mp-ℕ {P = P} P? _ = go 0 where
  go : ℕ → ∃ λ n → ¬ P n
  go n with P? n
  ... | inj₁ _   = go (suc n)
  ... | inj₂ ¬Pn = n , ¬Pn
