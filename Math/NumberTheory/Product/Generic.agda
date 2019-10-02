{-# OPTIONS --without-K --safe #-}

module Math.NumberTheory.Product.Generic where

-- agda-stdlib
open import Algebra

-- agda-misc
open import Math.NumberTheory.Summation.Generic

-- TODO add syntax
module MonoidProduct {c e} (M : Monoid c e) =
  MonoidSummation M
  renaming
  ( Σ< to Π<
  ; Σ≤ to Π≤
  ; Σ<range to Π<range
  ; Σ≤range to Π≤range
  )
  using ()
