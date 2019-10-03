{-# OPTIONS --without-K --safe #-}

module Math.NumberTheory.Summation.Nat where

-- agda-stdlib
open import Algebra
open import Data.Nat
open import Data.Nat.Properties
open import Relation.Binary.PropositionalEquality
open import Function.Core

-- agda-misc
open import Math.NumberTheory.Summation.Generic

-- DO NOT change this line
open MonoidSummation (Semiring.+-monoid *-+-semiring) public