-- https://github.com/idris-lang/Idris-dev/blob/4e704011fb805fcb861cc9a1bd68a2e727cefdde/libs/contrib/Data/Nat/Fib.idr
{-# OPTIONS --without-K --safe #-}
open import Relation.Binary.PropositionalEquality
open import Algebra.FunctionProperties

module Math.NumberTheory.Fibonacci.Generic
  {a} {A : Set a} {_∙_ : A → A → A}
  (∙-assoc : Associative _≡_ _∙_) (∙-comm : Commutative _≡_ _∙_)
  (v0 : A) (v1 : A)
  where

open import Data.Nat
open import Function

fibRec : ℕ → A
fibRec 0             = v0
fibRec 1             = v1
fibRec (suc (suc n)) = fibRec (suc n) ∙ fibRec n

fibAcc : ℕ → A → A → A
fibAcc 0       a b = a
fibAcc (suc n) a b = fibAcc n b (a ∙ b)

fib : ℕ → A
fib n = fibAcc n v0 v1

lemma : ∀ m n o p → (m ∙ n) ∙ (o ∙ p) ≡ (m ∙ o) ∙ (n ∙ p)
lemma m n o p = begin
  (m ∙ n) ∙ (o ∙ p) ≡⟨ ∙-assoc m n (o ∙ p)  ⟩
  m ∙ (n ∙ (o ∙ p)) ≡⟨ sym $ cong (m ∙_) $ ∙-assoc n o p ⟩
  m ∙ ((n ∙ o) ∙ p) ≡⟨ cong (λ v → m ∙ (v ∙ p)) $ ∙-comm n o ⟩
  m ∙ ((o ∙ n) ∙ p) ≡⟨ cong (m ∙_) $ ∙-assoc o n p ⟩
  m ∙ (o ∙ (n ∙ p)) ≡⟨ sym $ ∙-assoc m o (n ∙ p) ⟩
  (m ∙ o) ∙ (n ∙ p) ∎
  where open ≡-Reasoning

fibAdd : ∀ m n o p q → fibAcc m n o ∙ fibAcc m p q ≡ fibAcc m (n ∙ p) (o ∙ q)
fibAdd 0             n o p q = refl
fibAdd 1             n o p q = refl
fibAdd (suc (suc m)) n o p q = begin
  fibAcc (2 + m) n o ∙ fibAcc (2 + m) p q                         ≡⟨⟩
  fibAcc (1 + m) o (n ∙ o) ∙ fibAcc (1 + m) q (p ∙ q)             ≡⟨⟩
  fibAcc m (n ∙ o) (o ∙ (n ∙ o)) ∙ fibAcc m (p ∙ q) (q ∙ (p ∙ q)) ≡⟨ fibAdd m (n ∙ o) (o ∙ (n ∙ o)) (p ∙ q) (q ∙ (p ∙ q)) ⟩
  fibAcc m ((n ∙ o) ∙ (p ∙ q)) ((o ∙ (n ∙ o)) ∙ (q ∙ (p ∙ q)))    ≡⟨ cong₂ (fibAcc m) (lemma n o p q) (lemma o (n ∙ o) q (p ∙ q)) ⟩
  fibAcc m ((n ∙ p) ∙ (o ∙ q)) ((o ∙ q) ∙ ((n ∙ o) ∙ (p ∙ q)))    ≡⟨ cong (λ v → fibAcc m ((n ∙ p) ∙ (o ∙ q)) ((o ∙ q) ∙ v)) $ lemma n o p q ⟩
  fibAcc m ((n ∙ p) ∙ (o ∙ q)) ((o ∙ q) ∙ ((n ∙ p) ∙ (o ∙ q)))    ≡⟨⟩
  fibAcc (1 + m) (o ∙ q) ((n ∙ p) ∙ (o ∙ q))                      ≡⟨⟩
  fibAcc (2 + m) (n ∙ p) (o ∙ q)                                  ∎
  where open ≡-Reasoning

fibRec≡fib : ∀ n → fibRec n ≡ fib n
fibRec≡fib 0             = refl
fibRec≡fib 1             = refl
fibRec≡fib (suc (suc n)) = begin
  fibRec (2 + n)                         ≡⟨⟩
  fibRec (1 + n) ∙ fibRec n              ≡⟨ cong₂ _∙_ (fibRec≡fib (suc n)) (fibRec≡fib n) ⟩
  fib (1 + n) ∙ fib n                    ≡⟨⟩
  fibAcc (1 + n) v0 v1 ∙ fibAcc n v0 v1  ≡⟨⟩
  fibAcc n v1 (v0 ∙ v1) ∙ fibAcc n v0 v1 ≡⟨ fibAdd n v1 (v0 ∙ v1) v0 v1 ⟩
  fibAcc n (v1 ∙ v0) ((v0 ∙ v1) ∙ v1)    ≡⟨ cong₂ (fibAcc n) (∙-comm v1 v0) (trans (cong (_∙ v1) (∙-comm v0 v1)) (∙-assoc v1 v0 v1)) ⟩
  fibAcc n (v0 ∙ v1) (v1 ∙ (v0 ∙ v1))    ≡⟨⟩
  fib (2 + n)                            ∎
  where open ≡-Reasoning

fib-rec : ∀ n → fib (suc (suc n)) ≡ fib (suc n) ∙ fib n
fib-rec n = trans (sym $ fibRec≡fib (suc (suc n)))
                  (cong₂ _∙_ (fibRec≡fib (suc n)) (fibRec≡fib n))
