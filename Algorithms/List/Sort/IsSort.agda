{-# OPTIONS --without-K --safe #-}

open import Relation.Binary

module Algorithms.List.Sort.IsSort {c l₁ l₂} (DTO : DecTotalOrder c l₁ l₂) where

open import Level
open import Data.List
import      Data.List.Relation.Binary.Equality.Setoid as SetoidEquality
import      Data.List.Relation.Binary.Permutation.Setoid as PermutationSetoid
open import Data.List.Relation.Unary.Linked as Linked

import Algorithms.List.Sort.Insertion as I
import Algorithms.List.Sort.Insertion.Properties as Iₚ

open DecTotalOrder DTO renaming (Carrier to A)
open PermutationSetoid Eq.setoid
open SetoidEquality Eq.setoid

Sorted : List A → Set _
Sorted = Linked _≤_

record IsSort (sort : List A → List A) : Set (c ⊔ l₁ ⊔ l₂) where
  field
    sorted : (xs : List A) → Sorted (sort xs)
    perm   : (xs : List A) → sort xs ↭ xs

  open I.InsertionSortOperation _≤?_ renaming (sort to Isort)
  open Iₚ DTO
  private
    sort-Isort : ∀ xs → sort xs ≋ Isort xs
    sort-Isort xs =
      isSorted-unique (↭-trans (perm xs) (↭-sym (sort-permutation xs)))
      (sorted xs)
      (sort-isSorted xs)

  {-
  sort-id : ∀ {xs} → Linked _≤_ xs → sort xs ≋ xs
  sort-id = ?
  sort-cong-↭-≋ : ∀ {xs ys} → xs ↭ ys → sort xs ≋ sort ys
  sort-cong-↭-≋ = ?
  -}

-- isSort-unique : ∀ {sort₁ sort₂ : List A → List A} →
--                 IsSort sort₁ → IsSort sort₂ → ∀ xs → sort₁ xs ≋ sort₂ xs
