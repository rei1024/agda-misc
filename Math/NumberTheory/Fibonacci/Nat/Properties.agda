-- Properties of Fibonacci nunmbers

{-# OPTIONS --without-K --safe #-}

module Math.NumberTheory.Fibonacci.Nat.Properties where

-- agda-stdlib
open import Data.Unit using (tt)
open import Data.Sum
open import Data.Nat
open import Data.Nat.Properties
open import Relation.Nullary
open import Relation.Nullary.Decidable
open import Relation.Binary.PropositionalEquality
open import Function.Base

-- agda-misc
open import Math.NumberTheory.Fibonacci.Nat
open import Math.NumberTheory.Summation.Nat

open ≤-Reasoning

1≤fib[1+n] : ∀ n → 1 ≤ fib (suc n)
1≤fib[1+n] zero    = ≤-refl
1≤fib[1+n] (suc n) = begin
  1                   ≤⟨ 1≤fib[1+n] n ⟩
  fib (suc n)         ≤⟨ m≤m+n (fib (suc n)) (fib n) ⟩
  fib (suc n) + fib n ≡⟨ fib[1+n]+fib[n]≡fib[2+n] n ⟩
  fib (suc (suc n))   ∎

fib[n]<fib[1+n] : ∀ n {_ : True (2 ≤? n)} → fib n < fib (suc n)
fib[n]<fib[1+n] (suc (suc zero))    {wit} = s≤s (s≤s z≤n)
fib[n]<fib[1+n] (suc (suc (suc n))) {wit} = begin-strict
  fib (3 + n)               <⟨ ≤-refl ⟩
  1 + fib (3 + n)           ≡⟨ +-comm 1 (fib (3 + n)) ⟩
  fib (3 + n) + 1           ≤⟨ +-monoʳ-≤ (fib (3 + n)) (1≤fib[1+n] (suc n)) ⟩
  fib (3 + n) + fib (2 + n) ≡⟨ fib[1+n]+fib[n]≡fib[2+n] (2 + n) ⟩
  fib (4 + n)               ∎

private
  fib-mono-<-lemma : ∀ m n {_ : True (2 ≤? n)} → fib n < fib (suc m + n)
  fib-mono-<-lemma zero    n               {wit} = fib[n]<fib[1+n] n {wit}
  fib-mono-<-lemma (suc m) n@(suc (suc _)) {wit} = begin-strict
    fib n                           <⟨ fib-mono-<-lemma m n {tt} ⟩
    fib (1 + (m + n))               ≤⟨ m≤m+n (fib (1 + (m + n))) (fib (m + n)) ⟩
    fib (1 + (m + n)) + fib (m + n) ≡⟨ fib[1+n]+fib[n]≡fib[2+n] (m + n) ⟩
    fib (2 + (m + n))               ∎

fib-mono-< : ∀ m n {_ : True (2 ≤? m)} → m < n → fib m < fib n
fib-mono-< m n {wit} m<n = begin-strict
  fib m           <⟨ fib-mono-<-lemma o m {wit} ⟩
  fib (1 + o + m) ≡⟨ cong fib (sym $ n≡1+o+m) ⟩
  fib n           ∎
  where
  o = n ∸ suc m
  n≡1+o+m : n ≡ 1 + o + m
  n≡1+o+m = trans (sym $ m+[n∸m]≡n m<n) (cong suc (+-comm m o))

private
  ≤⇒≡∨< : ∀ {m n} → m ≤ n → (m ≡ n) ⊎ (m < n)
  ≤⇒≡∨< {m} {n} m≤n with m ≟ n
  ... | yes m≡n = inj₁ m≡n
  ... | no  m≢n = inj₂ (≤∧≢⇒< m≤n m≢n)

fib-mono-≤ : ∀ m n → m ≤ n → fib m ≤ fib n
fib-mono-≤ zero            n       m≤n = z≤n
fib-mono-≤ (suc zero)      (suc n) m≤n = 1≤fib[1+n] n
fib-mono-≤ m@(suc (suc _)) n       m≤n with ≤⇒≡∨< m≤n
... | inj₁ m≡n = ≤-reflexive (cong fib m≡n)
... | inj₂ m<n = <⇒≤ $ fib-mono-< m n {tt} m<n

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
    ≡⟨ cong (_∸ 1) $ fib[n]+fib[1+n]≡fib[2+n] (suc n) ⟩
  fib (3 + n) ∸ 1
    ∎
