-- Example usage of solver

{-# OPTIONS --without-K --safe #-}

open import Categories.Category
open import Categories.Category.Cartesian

module Experiment.Categories.Solver.Category.Cartesian.Example
  {o ℓ e} {𝒞 : Category o ℓ e} (cartesian : Cartesian 𝒞) where

open import Experiment.Categories.Solver.Category.Cartesian cartesian

open Category 𝒞
open Cartesian cartesian
open HomReasoning

private
  variable
    A B C D E F : Obj

module _ {f : D ⇒ E} {g : C ⇒ D} {h : B ⇒ C} {i : A ⇒ B} where
  _ : (f ∘ g) ∘ id ∘ h ∘ i ≈ f ∘ (g ∘ h) ∘ i
  _ = solve ((∥ f ∥ :∘ ∥ g ∥) :∘ :id :∘ ∥ h ∥ :∘ ∥ i ∥)
            (∥ f ∥ :∘ (∥ g ∥ :∘ ∥ h ∥) :∘ ∥ i ∥)
            refl

swap∘swap≈id : ∀ {A B} → swap {A}{B} ∘ swap {B}{A} ≈ id
swap∘swap≈id {A} {B} = solve (:swap {∥ A ∥} {∥ B ∥} :∘ :swap) :id refl

assocʳ∘assocˡ≈id : ∀ {A B C} → assocʳ {A}{B}{C} ∘ assocˡ {A}{B}{C} ≈ id
assocʳ∘assocˡ≈id {A} {B} {C} =
  solve (:assocʳ {∥ A ∥} {∥ B ∥} {∥ C ∥} :∘ :assocˡ) :id refl

module _ {f : B ⇒ C} (f′ : A ⇒ B) {g : E ⇒ F} {g′ : D ⇒ E} where
  ⁂-∘ : (f ⁂ g) ∘ (f′ ⁂ g′) ≈ (f ∘ f′) ⁂ (g ∘ g′)
  ⁂-∘ = solve lhs rhs refl where
    lhs = (∥ f ∥ :⁂ ∥ g ∥) :∘ (∥ f′ ∥ :⁂ ∥ g′ ∥)
    rhs = (∥ f ∥ :∘ ∥ f′ ∥) :⁂ (∥ g ∥ :∘ ∥ g′ ∥)

module _ {A B C D} where
  pentagon′ : (id ⁂ assocˡ) ∘ assocˡ ∘ (assocˡ ⁂ id) ≈
              assocˡ ∘ assocˡ {A × B} {C} {D}
  pentagon′ = solve lhs rhs refl where
    lhs = (:id :⁂ :assocˡ) :∘ :assocˡ :∘ (:assocˡ :⁂ :id)
    rhs = :assocˡ :∘ :assocˡ {∥ A ∥ :× ∥ B ∥} {∥ C ∥} {∥ D ∥}

module _ {A B C} where
  hexagon₁′ : (id ⁂ swap) ∘ assocˡ ∘ (swap ⁂ id) ≈
              assocˡ ∘ swap ∘ assocˡ {A}{B}{C}
  hexagon₁′ = solve lhs rhs refl where
    lhs = (:id :⁂ :swap) :∘ :assocˡ :∘ (:swap :⁂ :id)
    rhs = :assocˡ :∘ :swap :∘ :assocˡ {∥ A ∥}{∥ B ∥}{∥ C ∥}

module _ {f : A ⇒ B} where
  commute : ⟨ ! , id ⟩ ∘ f ≈ ⟨ id ∘ π₁ , f ∘ π₂ ⟩ ∘ ⟨ ! , id ⟩
  commute = solve (:⟨ :! , :id ⟩ :∘ ∥ f ∥)
                  (:⟨ :id :∘ :π₁ , ∥ f ∥ :∘ :π₂ ⟩ :∘ :⟨ :! , :id ⟩)
                  refl

_ : id {⊤} ≈ !
_ = solve (∥ id !∥) :! refl

_ : π₁ {⊤} {⊤} ≈ π₂
_ = solve (:π₁ {:⊤} {:⊤}) :π₂ refl

module _ {f : A ⇒ B} {g : C ⇒ D} where
  first↔second′ : first f ∘ second g ≈ second g ∘ first f
  first↔second′ = solve (:first ∥ f ∥ :∘ :second ∥ g ∥)
                        (:second ∥ g ∥ :∘ :first ∥ f ∥)
                        refl
