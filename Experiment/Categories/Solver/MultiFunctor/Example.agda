-- Example usage of solver

{-# OPTIONS --without-K --safe #-}

module Experiment.Categories.Solver.MultiFunctor.Example {o ℓ e} where

open import Categories.Category
open import Categories.Functor renaming (id to idF)
open import Experiment.Categories.Solver.MultiFunctor {o} {ℓ} {e}

module _ {𝒞 𝒟 ℰ : Category o ℓ e} (F : Functor 𝒞 𝒟) (G : Functor 𝒟 ℰ) where
  module F = Functor F
  module G = Functor G
  module 𝒞 = Category 𝒞
  module 𝒟 = Category 𝒟
  open Category ℰ
  open HomReasoning
  module _ {A B C D}
           (f : 𝒞 [ C , D ]) (g : 𝒞 [ B , C ]) (h : 𝒟 [ A , F.F₀ B ]) where
    _ : G.F₁ (F.F₁ f) ∘ G.F₁ 𝒟.id ∘ G.F₁ (F.F₁ g) ∘ G.F₁ h ≈
        G.F₁ (𝒟 [ F.F₁ (𝒞 [ f ∘ g ]) ∘ h ])
    _ = solve (:F₁ G (:F₁ F ∥-∥) :∘ :F₁ G :id :∘ :F₁ G (:F₁ F ∥-∥) :∘ :F₁ G ∥-∥)
              (:F₁ G (:F₁ F (∥-∥ :∘ ∥-∥) :∘ ∥-∥))
              refl
