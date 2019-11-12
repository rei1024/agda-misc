{-# OPTIONS --without-K --safe #-}

open import Relation.Binary

module Algorithms.List.Sort.Common
  {c l₁ l₂} (DTO : DecTotalOrder c l₁ l₂)
  where

-- agda-stdlib
open import Data.List
import Data.List.Relation.Binary.Equality.Setoid as ListSetoidEquality
open import Data.List.Relation.Unary.AllPairs
open import Data.List.Relation.Unary.Linked
import Data.List.Relation.Unary.Linked.Properties as Linkedₚ

-- agda-misc
open import Experiment.ListRelationProperties using (Linked-resp-≋)

open DecTotalOrder DTO
open ListSetoidEquality Eq.setoid

Sorted : List Carrier → Set _
Sorted = Linked _≤_

toAllPairs : ∀ {xs} → Sorted xs → AllPairs _≤_ xs
toAllPairs = Linkedₚ.Linked⇒AllPairs trans

Sorted-resp-≋ : ∀ {xs ys} → xs ≋ ys → Sorted xs → Sorted ys
Sorted-resp-≋ = Linked-resp-≋ Eq.setoid ≤-resp-≈
