{-# OPTIONS --without-K --safe #-}

module Math.NumberTheory.Fibonacci.Nat.Properties where

-- agda-stdlib
open import Data.Nat
open import Data.Nat.Properties
open import Relation.Binary.PropositionalEquality
open import Function.Core

-- agda-misc
open import Math.NumberTheory.Fibonacci.Nat
open import Math.NumberTheory.Summation.Nat

open ≤-Reasoning

1≤fib[1+n] : ∀ n → 1 ≤ fib (suc n)
1≤fib[1+n] zero    = ≤-refl
1≤fib[1+n] (suc n) = begin
  1 ≤⟨ 1≤fib[1+n] n ⟩
  fib (suc n) ≤⟨ m≤m+n (fib (suc n)) (fib n) ⟩
  fib (suc n) + fib n ≡⟨ sym $ fib-rec n ⟩
  fib (suc (suc n)) ∎

sum-of-fib : ∀ n → Σ[ k ≤ n ] fib k ≡ fib (2 + n) ∸ 1
sum-of-fib zero    = refl
sum-of-fib (suc n) = begin-equality
  Σ[ k ≤ n ] fib k + fib (suc n)
    ≡⟨ cong (_+ fib (suc n)) $ sum-of-fib n ⟩
  (fib (2 + n) ∸ 1) + fib (1 + n)
    ≡⟨ +-comm (fib (2 + n) ∸ 1) (fib (1 + n)) ⟩
  fib (1 + n) + (fib (2 + n) ∸ 1)
    ≡⟨ sym $ +-∸-assoc (fib (1 + n)) (1≤fib[1+n] (suc n)) ⟩
  (fib (1 + n) + fib (2 + n)) ∸ 1
    ≡⟨ cong (_∸ 1) $ +-comm (fib (1 + n)) (fib (2 + n)) ⟩
  (fib (2 + n) + fib (1 + n)) ∸ 1
    ≡⟨ sym $ cong (_∸ 1) $ fib-rec (suc n) ⟩
  fib (3 + n) ∸ 1
    ∎
