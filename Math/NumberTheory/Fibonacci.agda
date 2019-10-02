{-# OPTIONS --without-K --safe #-}

module Math.NumberTheory.Fibonacci where

open import Data.Nat
open import Data.Nat.Properties
open import Relation.Binary.PropositionalEquality

open import Math.NumberTheory.Fibonacci.Generic +-assoc +-comm 0 1 public
