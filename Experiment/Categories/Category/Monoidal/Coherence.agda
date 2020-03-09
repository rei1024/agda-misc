{-# OPTIONS --without-K --safe #-}

open import Categories.Category
open import Categories.Category.Monoidal

module Experiment.Categories.Category.Monoidal.Coherence
  {o ℓ e} {𝒞 : Category o ℓ e} (M : Monoidal 𝒞) where

open import Level
open import Data.Product using (Σ)

open import Categories.Morphism 𝒞
open import Categories.Functor

open Category 𝒞
open Monoidal M

𝒞′ : Category (o ⊔ ℓ ⊔ e) (ℓ ⊔ o) e
𝒞′ = categoryHelper record
  { Obj       = Σ (Endofunctor 𝒞) λ E →
     ∀ {A B} → Functor.F₀ E A ⊗₀ B ≅ Functor.F₀ E (A ⊗₀ B)
     -- TODO and more coherence
  ; _⇒_       = {!   !}
  ; _≈_       = {!   !}
  ; id        = {!   !}
  ; _∘_       = {!   !}
  ; assoc     = {!   !}
  ; identityˡ = {!   !}
  ; identityʳ = {!   !}
  ; equiv     = {!   !}
  ; ∘-resp-≈  = {!   !}
  }
