{-# OPTIONS --without-K --safe #-}

module Math.NumberTheory.Summation.Nat where

-- agda-stdlib
open import Algebra
open import Data.Nat.Properties

-- agda-misc
open import Math.NumberTheory.Summation.Generic

-- DO NOT change this line
open MonoidSummation (Semiring.+-monoid *-+-semiring) public
