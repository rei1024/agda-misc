-- Solver for Functor

{-# OPTIONS --without-K --safe #-}

open import Categories.Category
open import Categories.Functor renaming (id to idF)

module Experiment.Categories.Solver.Functor
  {o ℓ e o′ ℓ′ e′} {𝒞 : Category o ℓ e} {𝒟 : Category o′ ℓ′ e′}
  (F : Functor 𝒞 𝒟)
  where

open import Level
open import Relation.Binary using (Rel)

import Categories.Morphism.Reasoning as MR

import Experiment.Categories.Solver.Category

module 𝒞 = Category 𝒞
module CS = Experiment.Categories.Solver.Category 𝒞
open CS using (:id; _:∘_; ∥_∥) renaming (∥-∥ to ∥-∥′) public

open Category 𝒟
open HomReasoning
open MR 𝒟

open Functor F

private
  variable
    A B C D E : Obj

infixr 9 _:∘_

data Expr : Rel Obj (o ⊔ o′ ⊔ ℓ ⊔ ℓ′) where
  :id  : Expr A A
  _:∘_ : Expr B C → Expr A B → Expr A C
  :F₁  : ∀ {A B} → CS.Expr A B → Expr (F₀ A) (F₀ B)
  ∥_∥  : A ⇒ B → Expr A B

-- Semantics
⟦_⟧ : Expr A B → A ⇒ B
⟦ :id      ⟧ = id
⟦ e₁ :∘ e₂ ⟧ = ⟦ e₁ ⟧ ∘ ⟦ e₂ ⟧
⟦ :F₁ e    ⟧ = F₁ CS.⟦ e ⟧
⟦ ∥ f ∥    ⟧ = f

F₁⟦_⟧N∘_ : ∀ {B C} → CS.Expr B C → A ⇒ F₀ B → A ⇒ F₀ C
F₁⟦ :id      ⟧N∘ g = g
F₁⟦ e₁ :∘ e₂ ⟧N∘ g = F₁⟦ e₁ ⟧N∘ (F₁⟦ e₂ ⟧N∘ g)
F₁⟦ ∥ f ∥    ⟧N∘ g = F₁ f ∘ g

⟦_⟧N∘_ : Expr B C → A ⇒ B → A ⇒ C
⟦ :id      ⟧N∘ g = g
⟦ e₁ :∘ e₂ ⟧N∘ g = ⟦ e₁ ⟧N∘ (⟦ e₂ ⟧N∘ g)
⟦ :F₁ e    ⟧N∘ g = F₁⟦ e ⟧N∘ g
⟦ ∥ f ∥    ⟧N∘ g = f ∘ g

⟦_⟧N : Expr A B → A ⇒ B
⟦ e ⟧N = ⟦ e ⟧N∘ id

F₁⟦e⟧N∘f≈F₁⟦e⟧∘f : ∀ {B C} (e : CS.Expr B C) (g : A ⇒ F₀ B) →
                   F₁⟦ e ⟧N∘ g ≈ F₁ CS.⟦ e ⟧ ∘ g
F₁⟦e⟧N∘f≈F₁⟦e⟧∘f :id        g = begin
  g           ≈˘⟨ identityˡ ⟩
  id ∘ g      ≈˘⟨ identity ⟩∘⟨refl ⟩
  F₁ 𝒞.id ∘ g ∎
F₁⟦e⟧N∘f≈F₁⟦e⟧∘f (e₁ :∘ e₂) g = begin
  F₁⟦ e₁ ⟧N∘ (F₁⟦ e₂ ⟧N∘ g)         ≈⟨ F₁⟦e⟧N∘f≈F₁⟦e⟧∘f e₁ (F₁⟦ e₂ ⟧N∘ g) ⟩
  F₁ CS.⟦ e₁ ⟧ ∘ (F₁⟦ e₂ ⟧N∘ g)     ≈⟨ pushʳ (F₁⟦e⟧N∘f≈F₁⟦e⟧∘f e₂ g) ⟩
  (F₁ CS.⟦ e₁ ⟧ ∘ F₁ CS.⟦ e₂ ⟧) ∘ g ≈˘⟨ homomorphism ⟩∘⟨refl ⟩
  F₁ (CS.⟦ e₁ ⟧ 𝒞.∘ CS.⟦ e₂ ⟧) ∘ g ∎
F₁⟦e⟧N∘f≈F₁⟦e⟧∘f ∥ x ∥      g = refl

⟦e⟧N∘f≈⟦e⟧∘f : (e : Expr B C) (g : A ⇒ B) → ⟦ e ⟧N∘ g ≈ ⟦ e ⟧ ∘ g
⟦e⟧N∘f≈⟦e⟧∘f :id        g = ⟺ identityˡ
⟦e⟧N∘f≈⟦e⟧∘f (e₁ :∘ e₂) g = begin
  ⟦ e₁ ⟧N∘ (⟦ e₂ ⟧N∘ g) ≈⟨ ⟦e⟧N∘f≈⟦e⟧∘f e₁ (⟦ e₂ ⟧N∘ g) ⟩
  ⟦ e₁ ⟧ ∘ (⟦ e₂ ⟧N∘ g) ≈⟨ pushʳ (⟦e⟧N∘f≈⟦e⟧∘f e₂ g) ⟩
  (⟦ e₁ ⟧ ∘ ⟦ e₂ ⟧) ∘ g ∎
⟦e⟧N∘f≈⟦e⟧∘f (:F₁ e)    g = F₁⟦e⟧N∘f≈F₁⟦e⟧∘f e g
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
