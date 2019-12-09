-- Solver for Category

{-# OPTIONS --without-K --safe #-}

open import Categories.Category

module Experiment.Categories.Category.Solver {o ℓ e} (𝒞 : Category o ℓ e) where

open import Level
open import Relation.Binary using (Rel)

import Categories.Morphism.Reasoning as MR

open Category 𝒞
open HomReasoning
open MR 𝒞

private
  variable
    A B C D E : Obj

infixr 9 _:∘_

data Expr : Rel Obj (o ⊔ ℓ) where
  :id  : Expr A A
  _:∘_ : Expr B C → Expr A B → Expr A C
  ∥_∥  : A ⇒ B → Expr A B

⟦_⟧ : Expr A B → A ⇒ B
⟦ :id      ⟧ = id
⟦ e₁ :∘ e₂ ⟧ = ⟦ e₁ ⟧ ∘ ⟦ e₂ ⟧
⟦ ∥ f ∥    ⟧ = f

⟦_⟧N∘_ : Expr B C → A ⇒ B → A ⇒ C
⟦ :id      ⟧N∘ g = g
⟦ e₁ :∘ e₂ ⟧N∘ g = ⟦ e₁ ⟧N∘ (⟦ e₂ ⟧N∘ g)
⟦ ∥ f ∥    ⟧N∘ g = f ∘ g

⟦_⟧N : Expr A B → A ⇒ B
⟦ e ⟧N = ⟦ e ⟧N∘ id

⟦e⟧N∘f≈⟦e⟧∘f : (e : Expr B C) (g : A ⇒ B) → ⟦ e ⟧N∘ g ≈ ⟦ e ⟧ ∘ g
⟦e⟧N∘f≈⟦e⟧∘f :id        g = ⟺ identityˡ
⟦e⟧N∘f≈⟦e⟧∘f (e₁ :∘ e₂) g = begin
  ⟦ e₁ ⟧N∘ (⟦ e₂ ⟧N∘ g) ≈⟨ ⟦e⟧N∘f≈⟦e⟧∘f e₁ (⟦ e₂ ⟧N∘ g) ⟩
  ⟦ e₁ ⟧ ∘ (⟦ e₂ ⟧N∘ g) ≈⟨ pushʳ (⟦e⟧N∘f≈⟦e⟧∘f e₂ g) ⟩
  (⟦ e₁ ⟧ ∘ ⟦ e₂ ⟧) ∘ g ∎
⟦e⟧N∘f≈⟦e⟧∘f ∥ f ∥      g = refl

⟦e⟧N≈⟦e⟧ : (e : Expr A B) → ⟦ e ⟧N ≈ ⟦ e ⟧
⟦e⟧N≈⟦e⟧ e = ⟦e⟧N∘f≈⟦e⟧∘f e id ○ identityʳ

solve : (e₁ e₂ : Expr A B) → ⟦ e₁ ⟧N ≈ ⟦ e₂ ⟧N → ⟦ e₁ ⟧ ≈ ⟦ e₂ ⟧
solve e₁ e₂ eq = begin
  ⟦ e₁ ⟧  ≈˘⟨ ⟦e⟧N≈⟦e⟧ e₁ ⟩
  ⟦ e₁ ⟧N ≈⟨ eq ⟩
  ⟦ e₂ ⟧N ≈⟨ ⟦e⟧N≈⟦e⟧ e₂ ⟩
  ⟦ e₂ ⟧  ∎

∥-∥ : ∀ {f : A ⇒ B} → Expr A B
∥-∥ {f = f} = ∥ f ∥

private
  module _ (f : D ⇒ E) (g : C ⇒ D) (h : B ⇒ C) (i : A ⇒ B) where
    _ : (f ∘ id ∘ g) ∘ id ∘ h ∘ i ≈ f ∘ (g ∘ h) ∘ i
    _ = solve ((∥-∥ :∘ :id :∘ ∥-∥) :∘ :id :∘ ∥-∥ :∘ ∥-∥)
              (∥-∥ :∘ (∥-∥ :∘ ∥-∥) :∘ ∥-∥)
              refl
