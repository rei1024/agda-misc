-- Path induction

{-# OPTIONS --without-K --safe #-}

module Experiment.PropositionalEq where

open import Level renaming (zero to lzero; suc to lsuc)
open import Relation.Binary.PropositionalEquality
import Relation.Binary.Reasoning.Setoid as SetoidReasoning
open import Relation.Binary

private
  variable
    a c : Level
    A : Set a

-- HoTT 1.12.1
-- Path induction
PathInd : (C : (x y : A) → x ≡ y → Set c) →
          (∀ x → C x x refl) → ∀ x y (p : x ≡ y) → C x y p
PathInd C c x .x refl = c x

PathInd-refl : ∀ (C : (x y : A) → x ≡ y → Set c) (c : ∀ x → C x x refl) x →
            PathInd C c x x refl ≡ c x
PathInd-refl C c x = refl

-- Based path induction
BasedPathInd : (a : A) (C : ∀ x → a ≡ x → Set c) → C a refl →
               ∀ x (p : a ≡ x) → C x p
BasedPathInd a C c .a refl = c

BasedPathInd-refl : ∀ (a : A) (C : ∀ x → a ≡ x → Set c) (c : C a refl) →
                 BasedPathInd a C c a refl ≡ c
BasedPathInd-refl _ _ _ = refl
