{-# OPTIONS --without-K --safe #-}

module TypeTheory.HoTT.Data.Sum.Properties where

-- agda-stdlib
open import Level
open import Data.Empty
open import Data.Product
open import Data.Sum
open import Function.Base
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary

-- agda-misc
open import TypeTheory.HoTT.Base

private
  variable
    a b : Level
    A : Set a
    B : Set b

isProp-⊎ : ¬ (A × B) → isProp A → isProp B → isProp (A ⊎ B)
isProp-⊎ ¬[A×B] A-isP B-isP (inj₁ x₁) (inj₁ x₂) = cong inj₁ (A-isP x₁ x₂)
isProp-⊎ ¬[A×B] A-isP B-isP (inj₁ x₁) (inj₂ y₂) = ⊥-elim $ ¬[A×B] (x₁ , y₂)
isProp-⊎ ¬[A×B] A-isP B-isP (inj₂ y₁) (inj₁ x₂) = ⊥-elim $ ¬[A×B] (x₂ , y₁)
isProp-⊎ ¬[A×B] A-isP B-isP (inj₂ y₁) (inj₂ y₂) = cong inj₂ (B-isP y₁ y₂)
