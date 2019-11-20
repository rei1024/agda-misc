{-# OPTIONS --without-K --safe --exact-split #-}

module Constructive.Common where

open import Level
open import Data.Product
open import Data.Sum
open import Function.Base
open import Relation.Nullary

infix 2 _<=>_

-- Logical equivalence
_<=>_ : ∀ {a b} → Set a → Set b → Set (a ⊔ b)
A <=> B = (A → B) × (B → A)

module _ {a b} {A : Set a} {B : Set b} where
  mk<=> : (A → B) → (B → A) → A <=> B
  mk<=> = _,_

  fwd : A <=> B → A → B
  fwd = proj₁

  bwd : A <=> B → B → A
  bwd = proj₂

_∘<=>_ : ∀ {a b c} {A : Set a} {B : Set b} {C : Set c} →
         B <=> C → A <=> B → A <=> C
(f , g) ∘<=> (h , i) = f ∘ h , i ∘ g

Stable : ∀ {a} → Set a → Set a
Stable A = ¬ ¬ A → A

Dec⊎ : ∀ {a} → Set a → Set a
Dec⊎ A = A ⊎ ¬ A

-- Unary decidable predicate
DecU : ∀ {a p} {A : Set a} → (A → Set p) → Set (a ⊔ p)
DecU P = ∀ x → P x ⊎ ¬ P x

Inhabited : ∀ {a} → Set a → Set a
Inhabited A = A
