{-# OPTIONS --without-K --safe #-}
module Experiment.Transitive where

open import Level
open import Relation.Binary
open import Relation.Binary.Construct.Closure.Transitive
open import Relation.Binary.PropositionalEquality as ≡ using (_≡_)

private
  variable
    a b r : Level
    A B : Set a
    R S : Rel A r

fold : Transitive R → A [ R ]⁺ B → R A B
fold R-trans [ x∼y ]         = x∼y
fold R-trans (x ∼⁺⟨ x₁ ⟩ x₂) = R-trans (fold R-trans x₁) (fold R-trans x₂)

reverse : Symmetric R → A [ R ]⁺ B → B [ R ]⁺ A
reverse R-sym [ x∼y ] = [ R-sym x∼y ]
reverse R-sym (x ∼⁺⟨ x₁ ⟩ x₂) = _ ∼⁺⟨ reverse R-sym x₂ ⟩ reverse R-sym x₁

fold-reverse : (R-trans : Transitive R) (R-sym : Symmetric R) (xs : A [ R ]⁺ B) →
              (∀ {a b c} (x : R b c) (y : R a b) →
                R-trans (R-sym x) (R-sym y) ≡ R-sym (R-trans y x)) →
              fold R-trans (reverse R-sym xs) ≡ R-sym (fold R-trans xs)
fold-reverse R-trans R-sym [ x∼y ] homo = ≡.refl
fold-reverse R-trans R-sym (x ∼⁺⟨ xs₁ ⟩ xs₂) homo = begin
  R-trans (fold R-trans (reverse R-sym xs₂)) (fold R-trans (reverse R-sym xs₁))
    ≡⟨ ≡.cong₂ R-trans (fold-reverse R-trans R-sym xs₂ homo) (fold-reverse R-trans R-sym xs₁ homo) ⟩
  R-trans (R-sym (fold R-trans xs₂)) (R-sym (fold R-trans xs₁))
    ≡⟨ homo (fold R-trans xs₂) (fold R-trans xs₁) ⟩
  R-sym (R-trans (fold R-trans xs₁) (fold R-trans xs₂))
    ∎
  where
  open ≡.≡-Reasoning

-- map :
-- Star⇔ReflexiveTransitive : Star R x y ↔ Reflexive (Transitive R x y)

-- map-reverse : (RS : R ⊆ S) (R-sym : Symmetric R) (S-sym : Symmetric S) xs → map RS (reverse R-sym xs) ≡ reverse S-sym (map RS xs)
-- map-reverse R-sym xs = ?

-- ∘ᵢ-tc (reverse f⁺) ∘ᵢ ∘ᵢ-tc f⁺ ≃ ≅.refl
