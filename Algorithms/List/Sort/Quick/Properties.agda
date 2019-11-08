{-# OPTIONS --without-K --safe #-}

-- Properties of quicksort

open import Relation.Binary

module Algorithms.List.Sort.Quick.Properties
  {c l₁ l₂} (DTO : DecTotalOrder c l₁ l₂)
  where

-- agda-stdlib
open import Level
open import Data.List
import      Data.List.Properties as Listₚ
import Data.List.Relation.Binary.Permutation.Setoid as PermutationSetoid
open import Data.Product
import      Data.Nat as ℕ
open import Data.Nat.Induction as Ind
open import Relation.Binary as B
open import Relation.Unary as U
import      Relation.Unary.Properties as Uₚ
open import Relation.Binary.PropositionalEquality as P using (_≡_)
import Relation.Binary.Reasoning.Setoid as SetoidReasoning
open import Function.Core
open import Induction.WellFounded

-- agda-misc
open import Algorithms.List.Sort.Common DTO
open import Algorithms.List.Sort.Quick

open DecTotalOrder DTO renaming (Carrier to A)
open Quicksort _≤?_
open PermutationSetoid Eq.setoid
{-
sort-acc-filter : ∀ x xs rs lt₁ lt₂ →
  sort-acc (x ∷ xs) (acc rs) ≡
  sort-acc (filter (_≤? x) xs) (rs _ lt₁) ++ [ x ] ++
  sort-acc (filter (Uₚ.∁? (_≤? x)) xs) (rs _ lt₂)
sort-acc-filter x xs rs lt₁ lt₂ = begin
  sort-acc (proj₁ (split x xs)) (rs _ _) ++ [ x ] ++
    sort-acc (proj₂ (split x xs)) (rs _ _)
    ≡⟨ ? ⟩
  sort-acc (filter (_≤? x) xs) (rs _ lt₁) ++ [ x ] ++
    sort-acc (filter (Uₚ.∁? (_≤? x)) xs) (rs _ lt₂) ∎

sort-acc-permutation : ∀ xs ac → sort-acc xs ac ↭ xs
sort-acc-permutation []       ac       = ↭-refl
sort-acc-permutation (x ∷ xs) (acc rs) = begin
  sort-acc (x ∷ xs) (acc rs) ≈⟨ {!   !} ⟩
  x ∷ xs ∎
  where open SetoidReasoning ↭-setoid
-}
