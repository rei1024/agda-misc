{-# OPTIONS --without-K --safe #-}

open import Categories.Category
open import Categories.Category.Monoidal

module Experiment.Categories.Solver.Category.Monoidal
  {o ℓ e} {𝒞 : Category o ℓ e} (M : Monoidal 𝒞) where

open import Level
open import Relation.Binary using (Rel; REL)
open import Data.List

open import Categories.Morphism 𝒞

open Category 𝒞
open Monoidal M

infixr 10 _:⊗₀_ _:⊗₁_

data Sig : Set o where
  ∥_∥   : Obj → Sig
  :unit : Sig
  _:⊗₀_ : Sig → Sig → Sig

private
  variable
    A B C : Obj
    W X Y Z : Sig

data Expr : Rel Sig (o ⊔ ℓ) where
  :id  : Expr X X
  _:∘_ : Expr Y Z → Expr X Y → Expr X Z
  _:⊗₁_ : Expr X Y → Expr Z W → Expr (X :⊗₀ Z) (Y :⊗₀ W)
  :λ⇒ : Expr (:unit :⊗₀ X) X
  :λ⇐ : Expr X (:unit :⊗₀ X)
  :ρ⇒ : Expr (X :⊗₀ :unit) X
  :ρ⇐ : Expr X (X :⊗₀ :unit)
  :α⇒ : Expr ((X :⊗₀ Y) :⊗₀ Z) (X :⊗₀ (Y :⊗₀ Z))
  :α⇐ : Expr (X :⊗₀ (Y :⊗₀ Z)) ((X :⊗₀ Y) :⊗₀ Z)
  -- ∥_∥  : A ⇒ B → Expr ∥ A ∥ ∥ B ∥

NSig : Set o
NSig = List Obj

{-
data NExpr : REL Sig NSig (o ⊔ ℓ) where
  :id : NExpr ∥ A ∥ (A ∷ [])
  :λ⇒ : NExpr (:unit :⊗₀ X) (normaliseSig X)
-}

⟦_⟧Sig : Sig → Obj
⟦ ∥ A ∥   ⟧Sig = A
⟦ :unit   ⟧Sig = unit
⟦ X :⊗₀ Y ⟧Sig = ⟦ X ⟧Sig ⊗₀ ⟦ Y ⟧Sig

⟦_⟧NSig : NSig → Obj
⟦ []    ⟧NSig = unit
⟦ A ∷ X ⟧NSig = A ⊗₀ ⟦ X ⟧NSig

normaliseSig : Sig → NSig
normaliseSig ∥ A ∥     = A ∷ []
normaliseSig :unit     = []
normaliseSig (X :⊗₀ Y) = normaliseSig X ++ normaliseSig Y

private
  λ⇒ = unitorˡ.from
  λ⇐ = unitorˡ.to
  ρ⇒ = unitorʳ.from
  ρ⇐ = unitorʳ.to
  α⇒ = associator.from
  α⇐ = associator.to

⟦_⟧ : Expr X Y → ⟦ X ⟧Sig ⇒ ⟦ Y ⟧Sig
⟦ :id       ⟧ = id
⟦ e₁ :∘ e₂  ⟧ = ⟦ e₁ ⟧ ∘ ⟦ e₂ ⟧
⟦ e₁ :⊗₁ e₂ ⟧ = ⟦ e₁ ⟧ ⊗₁ ⟦ e₂ ⟧
⟦ :λ⇒       ⟧ = λ⇒
⟦ :λ⇐       ⟧ = λ⇐
⟦ :ρ⇒       ⟧ = ρ⇒
⟦ :ρ⇐       ⟧ = ρ⇐
⟦ :α⇒       ⟧ = α⇒
⟦ :α⇐       ⟧ = α⇐

⟦_⟧⁻¹ : Expr X Y → ⟦ Y ⟧Sig ⇒ ⟦ X ⟧Sig
⟦ :id       ⟧⁻¹ = id
⟦ e₁ :∘ e₂  ⟧⁻¹ = ⟦ e₂ ⟧⁻¹ ∘ ⟦ e₁ ⟧⁻¹
⟦ e₁ :⊗₁ e₂ ⟧⁻¹ = ⟦ e₁ ⟧⁻¹ ⊗₁ ⟦ e₂ ⟧⁻¹
⟦ :λ⇒       ⟧⁻¹ = λ⇐
⟦ :λ⇐       ⟧⁻¹ = λ⇒
⟦ :ρ⇒       ⟧⁻¹ = ρ⇐
⟦ :ρ⇐       ⟧⁻¹ = ρ⇒
⟦ :α⇒       ⟧⁻¹ = α⇐
⟦ :α⇐       ⟧⁻¹ = α⇒

⟦_⟧≅ : Expr X Y → ⟦ X ⟧Sig ≅ ⟦ Y ⟧Sig
⟦ :id       ⟧≅ = ≅.refl
⟦ e₁ :∘ e₂  ⟧≅ = ≅.trans ⟦ e₂ ⟧≅ ⟦ e₁ ⟧≅
⟦ e₁ :⊗₁ e₂ ⟧≅ = {!   !}
⟦ :λ⇒       ⟧≅ = {!   !}
⟦ :λ⇐       ⟧≅ = {!   !}
⟦ :ρ⇒       ⟧≅ = {!   !}
⟦ :ρ⇐       ⟧≅ = {!   !}
⟦ :α⇒       ⟧≅ = {!   !}
⟦ :α⇐       ⟧≅ = {!   !}


-- theorem : (e₁ e₂ : Expr S T) → ⟦ e₁ ⟧ ≈ ⟦ e₂ ⟧
-- lemma : Expr S T → ⟦ S ⟧Sig ≅ ⟦ T ⟧Sig
-- lemma : ⟦ normaliseSig S ⟧NSig ≅ ⟦ S ⟧Sig
-- resp : ⟦ S ⟧NSig ≅ ⟦ T ⟧NSig
-- lemma : Expr S T → normaliseSig S ≡ normaliseSig T
