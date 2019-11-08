{-# OPTIONS --without-K --safe #-}

open import Relation.Binary

module Algorithms.List.Sort.IsSort {c l₁ l₂} (DTO : DecTotalOrder c l₁ l₂) where

-- agda-stdlib
open import Level
import Relation.Binary.Reasoning.Setoid as SetoidReasoning
open import Data.List
import      Data.List.Relation.Binary.Equality.Setoid as SetoidEquality
import      Data.List.Relation.Binary.Permutation.Setoid as PermutationSetoid
open import Data.List.Relation.Unary.Linked as Linked

-- agda-misc
open import Algorithms.List.Sort.Common DTO
import Algorithms.List.Sort.Insertion as I
import Algorithms.List.Sort.Insertion.Properties as Iₚ

open DecTotalOrder DTO renaming (Carrier to A)
open PermutationSetoid Eq.setoid
open SetoidEquality Eq.setoid
open I.InsertionSortOperation _≤?_ renaming (sort to Isort)

record IsSort (sort : List A → List A) : Set (c ⊔ l₁ ⊔ l₂) where
  field
    sorted : (xs : List A) → Sorted (sort xs)
    perm   : (xs : List A) → sort xs ↭ xs

  open Iₚ DTO

  sort-Isort : ∀ xs → sort xs ≋ Isort xs
  sort-Isort xs =
    Sorted-unique (↭-trans (perm xs) (↭-sym (sort-permutation xs)))
                  (sorted xs)
                  (sort-Sorted xs)

isSort-unique : ∀ {sort₁ sort₂ : List A → List A} →
                IsSort sort₁ → IsSort sort₂ → ∀ xs → sort₁ xs ≋ sort₂ xs
isSort-unique {sort₁} {sort₂} sort₁-isSort sort₂-isSort xs = begin
  sort₁ xs ≈⟨ IsSort.sort-Isort sort₁-isSort xs ⟩
  Isort xs ≈⟨ ≋-sym (IsSort.sort-Isort sort₂-isSort xs) ⟩
  sort₂ xs ∎
  where open SetoidReasoning ≋-setoid
