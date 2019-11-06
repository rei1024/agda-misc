{-# OPTIONS --without-K --safe #-}

-- Insertion sort

module Algorithms.List.Sort.Insertion where

-- agda-stdlib
open import Level

open import Data.Bool hiding (_≤_; _≤?_; _<_)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.List
import      Data.List.Properties as Listₚ
import      Data.Nat as ℕ
import      Data.Nat.Properties as ℕₚ
open import Data.Product hiding (swap)

import      Data.List.Relation.Binary.Equality.Setoid as ListSetoidEquality
open import Data.List.Relation.Unary.All as All
import      Data.List.Relation.Unary.All.Properties as Allₚ
open import Data.List.Relation.Unary.Linked as Linked
import      Data.List.Relation.Unary.Linked.Properties as Linkedₚ
open import Data.List.Relation.Unary.AllPairs as AllPairs
import      Data.List.Relation.Unary.AllPairs.Properties as AllPairsₚ
import      Data.List.Relation.Binary.Permutation.Setoid as PermutationSetoid
import      Data.List.Relation.Binary.Permutation.Setoid.Properties
  as PermutationSetoidProperties

open import Function.Core using (_∘_; _$_; flip)

open import Relation.Binary as B
import      Relation.Binary.Properties.DecTotalOrder as DecTotalOrderProperties
open import Relation.Binary.PropositionalEquality using (_≡_)
import      Relation.Binary.PropositionalEquality as ≡ hiding ([_])
import      Relation.Binary.Reasoning.Setoid as SetoidReasoning
open import Relation.Nullary
open import Relation.Unary as U

-- agda-misc
open import Experiment.ListRelationProperties using (foldr-preservesʳ; Linked-∷⁻ʳ)

module InsertionSortOperation
  {a r} {A : Set a} {_≤_ : Rel A r} (_≤?_ : B.Decidable _≤_)
  where

  insert : A → List A → List A
  insert x []           = [ x ]
  insert x (y ∷ ys) with x ≤? y
  ... | true  because _ = x ∷ y ∷ ys
  ... | false because _ = y ∷ insert x ys

  -- | Insertion sort
  sort : List A → List A
  sort = foldr insert []

module Test where
  open InsertionSortOperation ℕ._≤?_

  _ : sort (5 ∷ 2 ∷ 4 ∷ 3 ∷ 1 ∷ []) ≡.≡ 1 ∷ 2 ∷ 3 ∷ 4 ∷ 5 ∷ []
  _ = ≡.refl
