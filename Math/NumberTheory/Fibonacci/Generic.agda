-- https://github.com/idris-lang/Idris-dev/blob/4e704011fb805fcb861cc9a1bd68a2e727cefdde/libs/contrib/Data/Nat/Fib.idr

{-# OPTIONS --without-K --safe #-}

-- agda-stdlib
open import Algebra

module Math.NumberTheory.Fibonacci.Generic
  {c e} (CM : CommutativeMonoid c e)
  (v0 v1 : CommutativeMonoid.Carrier CM)
  where

-- agda-stdlib
open import Data.Nat
open import Function
import Relation.Binary.Reasoning.Setoid as SetoidReasoning
import Relation.Binary.PropositionalEquality as ≡

open CommutativeMonoid CM
  renaming
  ( Carrier to A
  )

open SetoidReasoning setoid

fibRec : ℕ → A
fibRec 0             = v0
fibRec 1             = v1
fibRec (suc (suc n)) = fibRec (suc n) ∙ fibRec n

fibAcc : ℕ → A → A → A
fibAcc 0       a b = a
fibAcc (suc n) a b = fibAcc n b (a ∙ b)

fib : ℕ → A
fib n = fibAcc n v0 v1

lemma : ∀ m n o p → (m ∙ n) ∙ (o ∙ p) ≈ (m ∙ o) ∙ (n ∙ p)
lemma m n o p = begin
  (m ∙ n) ∙ (o ∙ p) ≈⟨ assoc m n (o ∙ p)  ⟩
  m ∙ (n ∙ (o ∙ p)) ≈⟨ sym $ ∙-congˡ $ assoc n o p ⟩
  m ∙ ((n ∙ o) ∙ p) ≈⟨ ∙-congˡ $ ∙-congʳ $ comm n o ⟩
  m ∙ ((o ∙ n) ∙ p) ≈⟨ ∙-congˡ $ assoc o n p ⟩
  m ∙ (o ∙ (n ∙ p)) ≈⟨ sym $ assoc m o (n ∙ p) ⟩
  (m ∙ o) ∙ (n ∙ p) ∎

fibAcc-cong : ∀ {m n o p q r} →
  m ≡.≡ n → o ≈ p → q ≈ r → fibAcc m o q ≈ fibAcc n p r
fibAcc-cong {zero}  {.0}       {o} {p} {q} {r} ≡.refl o≈p q≈r = o≈p
fibAcc-cong {suc m} {.(suc m)} {o} {p} {q} {r} ≡.refl o≈p q≈r =
  fibAcc-cong {m = m} ≡.refl q≈r (∙-cong o≈p q≈r)

fibAdd : ∀ m n o p q → fibAcc m n o ∙ fibAcc m p q ≈ fibAcc m (n ∙ p) (o ∙ q)
fibAdd 0             n o p q = refl
fibAdd 1             n o p q = refl
fibAdd (suc (suc m)) n o p q = begin
  fibAcc (2 + m) n o ∙ fibAcc (2 + m) p q                         ≡⟨⟩
  fibAcc (1 + m) o (n ∙ o) ∙ fibAcc (1 + m) q (p ∙ q)             ≡⟨⟩
  fibAcc m (n ∙ o) (o ∙ (n ∙ o)) ∙ fibAcc m (p ∙ q) (q ∙ (p ∙ q)) ≈⟨ fibAdd m (n ∙ o) (o ∙ (n ∙ o)) (p ∙ q) (q ∙ (p ∙ q)) ⟩
  fibAcc m ((n ∙ o) ∙ (p ∙ q)) ((o ∙ (n ∙ o)) ∙ (q ∙ (p ∙ q)))    ≈⟨ fibAcc-cong {m = m} ≡.refl (lemma n o p q) (lemma o (n ∙ o) q (p ∙ q)) ⟩
  fibAcc m ((n ∙ p) ∙ (o ∙ q)) ((o ∙ q) ∙ ((n ∙ o) ∙ (p ∙ q)))    ≈⟨ fibAcc-cong {m = m} ≡.refl refl (∙-congˡ $ lemma n o p q) ⟩
  fibAcc m ((n ∙ p) ∙ (o ∙ q)) ((o ∙ q) ∙ ((n ∙ p) ∙ (o ∙ q)))    ≡⟨⟩
  fibAcc (1 + m) (o ∙ q) ((n ∙ p) ∙ (o ∙ q))                      ≡⟨⟩
  fibAcc (2 + m) (n ∙ p) (o ∙ q)                                  ∎

fibRec≈fib : ∀ n → fibRec n ≈ fib n
fibRec≈fib 0             = refl
fibRec≈fib 1             = refl
fibRec≈fib (suc (suc n)) = begin
  fibRec (2 + n)                         ≡⟨⟩
  fibRec (1 + n) ∙ fibRec n              ≈⟨ ∙-cong (fibRec≈fib (suc n)) (fibRec≈fib n) ⟩
  fib (1 + n) ∙ fib n                    ≡⟨⟩
  fibAcc (1 + n) v0 v1 ∙ fibAcc n v0 v1  ≡⟨⟩
  fibAcc n v1 (v0 ∙ v1) ∙ fibAcc n v0 v1 ≈⟨ fibAdd n v1 (v0 ∙ v1) v0 v1 ⟩
  fibAcc n (v1 ∙ v0) ((v0 ∙ v1) ∙ v1)    ≈⟨ fibAcc-cong {m = n} ≡.refl (comm v1 v0) (trans (∙-congʳ (comm v0 v1)) (assoc v1 v0 v1)) ⟩
  fibAcc n (v0 ∙ v1) (v1 ∙ (v0 ∙ v1))    ≡⟨⟩
  fib (2 + n)                            ∎

fib[2+n]≈fib[1+n]∙fib[n] : ∀ n → fib (suc (suc n)) ≈ fib (suc n) ∙ fib n
fib[2+n]≈fib[1+n]∙fib[n] n =
  trans (sym $ fibRec≈fib (suc (suc n)))
        (∙-cong (fibRec≈fib (suc n)) (fibRec≈fib n))

fib[1+n]∙fib[n]≈fib[2+n] : ∀ n → fib (suc n) ∙ fib n ≈ fib (suc (suc n))
fib[1+n]∙fib[n]≈fib[2+n] n = sym $ fib[2+n]≈fib[1+n]∙fib[n] n

fib[n]∙fib[1+n]≈fib[2+n] : ∀ n → fib n ∙ fib (suc n) ≈ fib (suc (suc n))
fib[n]∙fib[1+n]≈fib[2+n] n = trans (comm (fib n) (fib (suc n))) (fib[1+n]∙fib[n]≈fib[2+n] n)
