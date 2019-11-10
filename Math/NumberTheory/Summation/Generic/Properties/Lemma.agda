{-# OPTIONS --without-K --safe #-}

module Math.NumberTheory.Summation.Generic.Properties.Lemma where

-- agda-stdlib
open import Data.Nat
open import Data.Nat.Properties
open import Data.Nat.Solver
open import Relation.Binary.PropositionalEquality
open import Function.Base

lemma₁ : ∀ m n → 2 + m + n ≡ suc m + suc n
lemma₁ = solve 2 (λ m n → con 2 :+ m :+ n := con 1 :+ m :+ (con 1 :+ n)) refl
  where open +-*-Solver
