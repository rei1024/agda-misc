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


module _ {A : Set a} {P : U.Pred A p} (P? : U.Decidable P) where
  partition₁-defn : ∀ xs → proj₁ (partition P? xs) ≡ filter P? xs
  partition₁-defn xs = P.cong proj₁ (Listₚ.partition-defn P? xs)

  partition₂-defn : ∀ xs → proj₂ (partition P? xs) ≡ filter (Uₚ.∁? P?) xs
  partition₂-defn xs = P.cong proj₂ (Listₚ.partition-defn P? xs)

  length-partition₁ : ∀ xs → length (proj₁ (partition P? xs)) ℕ.≤ length xs
  length-partition₁ xs =
    P.subst (ℕ._≤ length xs)
            (P.sym $ P.cong length $ partition₁-defn xs)
            (Listₚ.length-filter P? xs)

  length-partition₂ : ∀ xs → length (proj₂ (partition P? xs)) ℕ.≤ length xs
  length-partition₂ xs =
    P.subst (ℕ._≤ length xs)
            (P.sym $ P.cong length $ partition₂-defn xs)
            (Listₚ.length-filter (Uₚ.∁? P?) xs)

module Quicksort {A : Set a} {_≤_ : Rel A r} (_≤?_ : B.Decidable _≤_) where
  split : A → List A → List A × List A
  split x xs = partition (λ y → y ≤? x) xs

  _L<_ : Rel (List A) _
  _L<_ = ℕ._<_ on length

  sort-acc : ∀ xs → Acc _L<_ xs → List A
  sort-acc []       _        = []
  sort-acc (x ∷ xs) (acc rs) =
    sort-acc ys (rs _ (ℕ.s≤s $ length-partition₁ (_≤? x) xs)) ++
    [ x ] ++
    sort-acc zs (rs _ (ℕ.s≤s $ length-partition₂ (_≤? x) xs))
    where
    splitted = split x xs
    ys = proj₁ splitted
    zs = proj₂ splitted

  L<-wf : WellFounded _L<_
  L<-wf = InverseImage.wellFounded length Ind.<-wellFounded

  -- Quicksort
  sort : List A → List A
  sort xs = sort-acc xs (L<-wf xs)
