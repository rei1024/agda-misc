{-# OPTIONS --without-K --safe #-}

-- Quicksort

module Algorithms.List.Sort.Merge where

-- agda-stdlib
open import Level
open import Data.Bool using (true; false)
open import Data.List
import      Data.List.Properties as Listₚ
open import Data.Product as Prod
import      Data.Nat as ℕ
open import Data.Nat.Induction as Ind
open import Relation.Binary as B
open import Relation.Unary as U
open import Relation.Nullary
import      Relation.Unary.Properties as Uₚ
open import Relation.Binary.PropositionalEquality as P using (_≡_)
open import Function.Core
open import Induction.WellFounded

private
  variable
    a p r : Level

module _ {A : Set a} {_≤_ : Rel A r} (_≤?_ : B.Decidable _≤_) where
  merge′ : A → A → List A → List A → List A
  merge′ x y xs ys with x ≤? y
  merge′ x y []        ys | true because _ = x ∷ y ∷ ys
  merge′ x y (x₁ ∷ xs) ys | true because _ = x ∷ merge′ x₁ y xs ys
  merge′ x y xs []        | false because _ = y ∷ x ∷ xs
  merge′ x y xs (y₁ ∷ ys) | false because _ = y ∷ merge′ x y₁ xs ys

  merge : List A → List A → List A
  merge []       ys       = ys
  merge (x ∷ xs) []       = x ∷ xs
  merge (x ∷ xs) (y ∷ ys) = merge′ x y xs ys

  _L<_ : Rel (List A) _
  _L<_ = ℕ._<_ on length

  L<-wf : WellFounded _L<_
  L<-wf = InverseImage.wellFounded length Ind.<-wellFounded

  split : List A → (List A × List A)
  split [] = [] , []
  split (x ∷ []) = [ x ] , []
  split (x ∷ y ∷ xs) = Prod.map (x ∷_) (y ∷_) (split xs)

  sort : List A → List A
  sort [] = []
  sort (x ∷ xs) = {!   !}
  sort xs = split xs
  ys , zs = merge (sort ys) (sort zs)
