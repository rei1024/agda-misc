-- Example usage of solver

{-# OPTIONS --without-K --safe #-}

open import Categories.Category
open import Categories.Functor renaming (id to idF)

module Experiment.Categories.Solver.Functor.Example
  {o ℓ e o′ ℓ′ e′} {𝒞 : Category o ℓ e} {𝒟 : Category o′ ℓ′ e′}
  (F : Functor 𝒞 𝒟)
  where

open Category 𝒟
open HomReasoning
open Functor F

open import Experiment.Categories.Solver.Functor F

module _ {A B C D E}
         (f : 𝒞 [ D , E ]) (g : 𝒞 [ C , D ]) (h : 𝒞 [ B , C ]) (i : 𝒞 [ A , B ]) where
  _ : F₁ (f 𝒞.∘ g 𝒞.∘ h) ∘ F₁ 𝒞.id ∘ F₁ i ∘ id ≈ F₁ (f 𝒞.∘ g) ∘ F₁ (h 𝒞.∘ i)
  _ = solve (:F₁ (∥-∥′ :∘ ∥-∥′ :∘ ∥-∥′) :∘ :F₁ :id :∘ :F₁ (∥-∥′) :∘ :id)
            (:F₁ (∥-∥′ :∘ ∥-∥′) :∘ :F₁ (∥-∥′ :∘ ∥-∥′))
            refl
