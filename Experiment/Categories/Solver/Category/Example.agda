-- Example usage of solver

{-# OPTIONS --without-K --safe #-}

open import Categories.Category

module Experiment.Categories.Solver.Category.Example
  {o ℓ e} (𝒞 : Category o ℓ e) where

open import Experiment.Categories.Solver.Category 𝒞

open Category 𝒞
open HomReasoning

private
  variable
    A B C D E : Obj

module _ (f : D ⇒ E) (g : C ⇒ D) (h : B ⇒ C) (i : A ⇒ B) where
  _ : (f ∘ id ∘ g) ∘ id ∘ h ∘ i ≈ f ∘ (g ∘ h) ∘ i
  _ = solve ((∥-∥ :∘ :id :∘ ∥-∥) :∘ :id :∘ ∥-∥ :∘ ∥-∥)
            (∥-∥ :∘ (∥-∥ :∘ ∥-∥) :∘ ∥-∥)
            refl
