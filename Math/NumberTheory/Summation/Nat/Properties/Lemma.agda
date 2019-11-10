{-# OPTIONS --without-K --safe #-}

module Math.NumberTheory.Summation.Nat.Properties.Lemma where

-- agda-stdlib
open import Data.Nat
open import Data.Nat.Properties
open import Data.Nat.Solver
open import Relation.Binary.PropositionalEquality
open import Function.Base

lemma₁ : ∀ n → n * (1 + n) * (1 + 2 * n) + 6 * ((1 + n) ^ 2) ≡
               (1 + n) * (2 + n) * (1 + 2 * (1 + n))
lemma₁ = solve 1 (λ n →
  (n :* (con 1 :+ n) :* (con 1 :+ con 2 :* n) :+ con 6 :* (con 1 :+ n) :^ 2) :=
  (con 1 :+ n) :* (con 2 :+ n) :* (con 1 :+ con 2 :* (con 1 :+ n))
  ) refl
  where open +-*-Solver
