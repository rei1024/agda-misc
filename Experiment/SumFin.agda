
{-# OPTIONS --without-K --safe #-}

module Experiment.SumFin where

open import Data.Empty
open import Data.Unit
open import Data.Sum
open import Data.Nat
open import Data.Nat.Properties
open import Relation.Binary.PropositionalEquality

private
  variable
    k : ℕ

Fin : ℕ → Set
Fin zero    = ⊥
Fin (suc n) = ⊤ ⊎ (Fin n)

pattern fzero  = inj₁ tt
pattern fsuc n = inj₂ n

finj : Fin k → Fin (suc k)
finj {suc k} fzero    = fzero
finj {suc k} (fsuc n) = fsuc (finj {k} n)

toℕ : Fin k → ℕ
toℕ {suc k} (inj₁ tt) = zero
toℕ {suc k} (inj₂ x)  = suc (toℕ {k} x)

toℕ-injective : {m n : Fin k} → toℕ m ≡ toℕ n → m ≡ n
toℕ-injective {suc k} {fzero}  {fzero}  _ = refl
toℕ-injective {suc k} {fzero} {fsuc x} ()
toℕ-injective {suc k} {fsuc m} {fzero} ()
toℕ-injective {suc k} {fsuc m} {fsuc x} p = cong fsuc (toℕ-injective (suc-injective p))
