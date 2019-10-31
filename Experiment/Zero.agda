{-# OPTIONS --without-K --safe #-}

module Experiment.Zero where

data ⊥ : Set where

record ⊤ : Set where
  constructor tt

data Bool : Set where
  true false : Bool

data ℕ : Set where
  zero : ℕ
  suc  : ℕ → ℕ

data _≡_ {a} {A : Set a} (x : A) : A → Set a where
  refl : x ≡ x
