-- Homotopy type theory

-- https://github.com/agda/cubical

{-# OPTIONS --without-K --safe #-}

module TypeTheory.HoTT.Base where

-- agda-stdlib
open import Level renaming (zero to lzero; suc to lsuc)
open import Data.Product
open import Relation.Binary.PropositionalEquality

private
  variable
    a b : Level

fiber : {A : Set a} {B : Set b} (f : A → B) (y : B) → Set (a ⊔ b)
fiber f y = ∃ λ x → f x ≡ y

isContr : Set a → Set a
isContr A = Σ A λ x → ∀ y → x ≡ y

isProp : Set a → Set a
isProp A = (x y : A) → x ≡ y

isSet : Set a → Set a
isSet A = (x y : A) → isProp (x ≡ y)
