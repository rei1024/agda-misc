-- Quicksort

{-# OPTIONS --without-K --safe #-}

module Algorithms.List.Sort.Quick where

-- agda-stdlib
open import Level
open import Data.List
import      Data.List.Properties as Listₚ
open import Data.Product
import      Data.Nat as ℕ
open import Data.Nat.Induction as Ind
open import Relation.Binary as B
open import Relation.Binary.PropositionalEquality as P using (_≡_)
open import Relation.Unary as U
import      Relation.Unary.Properties as Uₚ
open import Function.Base
open import Induction.WellFounded

private
  variable
    a p r : Level

private
  module _ {A : Set a} {P : U.Pred A p} (P? : U.Decidable P) where
    length-partition₁ : ∀ xs → length (proj₁ (partition P? xs)) ℕ.≤ length xs
    length-partition₁ xs =
      P.subst (ℕ._≤ length xs)
              (P.sym $ P.cong (length ∘′ proj₁) $ Listₚ.partition-defn P? xs)
              (Listₚ.length-filter P? xs)

    length-partition₂ : ∀ xs → length (proj₂ (partition P? xs)) ℕ.≤ length xs
    length-partition₂ xs =
      P.subst (ℕ._≤ length xs)
              (P.sym $ P.cong (length ∘′ proj₂) $ Listₚ.partition-defn P? xs)
              (Listₚ.length-filter (Uₚ.∁? P?) xs)

module Quicksort {A : Set a} {_≤_ : Rel A r} (_≤?_ : B.Decidable _≤_) where
  split : A → List A → List A × List A
  split x xs = partition (λ y → y ≤? x) xs

  split-decr₁ : ∀ x xs → length (proj₁ (split x xs)) ℕ.≤ length xs
  split-decr₁ x xs = length-partition₁ (_≤? x) xs

  split-decr₂ : ∀ x xs → length (proj₂ (split x xs)) ℕ.≤ length xs
  split-decr₂ x xs = length-partition₂ (_≤? x) xs

  _L<_ : Rel (List A) _
  _L<_ = ℕ._<_ on length

  sort-acc : ∀ xs → Acc _L<_ xs → List A
  sort-acc []       _        = []
  sort-acc (x ∷ xs) (acc rs) =
    sort-acc (proj₁ splitted) (rs _ (ℕ.s≤s $ split-decr₁ x xs)) ++
    [ x ] ++
    sort-acc (proj₂ splitted) (rs _ (ℕ.s≤s $ split-decr₂ x xs))
    where
    splitted = split x xs

  L<-wf : WellFounded _L<_
  L<-wf = InverseImage.wellFounded length Ind.<-wellFounded

  -- Quicksort
  sort : List A → List A
  sort xs = sort-acc xs (L<-wf xs)
