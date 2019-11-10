{-# OPTIONS --without-K --safe #-}

-- Quicksort

module Experiment.Induction where

-- agda-stdlib
open import Level
open import Data.List
open import Data.Product
open import Data.Nat as ℕ
open import Data.Nat.Induction as Ind
open import Relation.Binary as B
open import Relation.Unary as U
import      Relation.Unary.Properties as Uₚ
open import Relation.Binary.PropositionalEquality as P using (_≡_)
open import Function.Base
open import Induction.WellFounded

private
  variable
    a p r : Level
