{-# OPTIONS --without-K --safe #-}

module Math.NumberTheory.Fibonacci.Nat where

-- agda-stdlib
open import Data.Nat
open import Data.Nat.Properties
open import Relation.Binary.PropositionalEquality

-- agda-misc
open import Math.NumberTheory.Fibonacci.Generic +-0-commutativeMonoid 0 1
  renaming
  ( fibRec≈fib to fibRec≡fib
  ; fib[2+n]≈fib[1+n]∙fib[n] to fib[2+n]≡fib[1+n]+fib[n]
  ; fib[1+n]∙fib[n]≈fib[2+n] to fib[1+n]+fib[n]≡fib[2+n]
  ; fib[n]∙fib[1+n]≈fib[2+n] to fib[n]+fib[1+n]≡fib[2+n]
  ) public
