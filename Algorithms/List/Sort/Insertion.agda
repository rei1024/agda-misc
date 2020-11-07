-- Insertion sort

{-# OPTIONS --without-K --safe #-}

module Algorithms.List.Sort.Insertion where

-- agda-stdlib
open import Data.Bool hiding (_≤_; _≤?_; _<_)
open import Data.List
import      Data.Nat as ℕ
open import Relation.Binary as B
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Relation.Nullary

module InsertionSortOperation
  {a r} {A : Set a} {_≤_ : Rel A r} (_≤?_ : B.Decidable _≤_)
  where

-- swap : A x A → A × A
-- swap ∘ swap ≡ id
-- ifTrueSwap : Bool → A × A → A × A
-- ifTrueSwap x ∘ ifTrueSwap y ≡ ifTrueSwap (xor x y)
-- x : A → A ≡ Unit ⊎ (Σ A (λ y → x ≢ y))

  insert : A → List A → List A
  insert x []           = [ x ]
  insert x (y ∷ ys) with x ≤? y
  ... | true  because _ = x ∷ y ∷ ys
  ... | false because _ = y ∷ insert x ys

  -- | Insertion sort
  sort : List A → List A
  sort = foldr insert []

private
  open InsertionSortOperation ℕ._≤?_

  _ : sort (5 ∷ 2 ∷ 4 ∷ 3 ∷ 1 ∷ []) ≡ 1 ∷ 2 ∷ 3 ∷ 4 ∷ 5 ∷ []
  _ = refl
