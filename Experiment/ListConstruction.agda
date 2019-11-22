{-# OPTIONS --without-K --safe #-}

module Experiment.ListConstruction where

open import Level renaming (zero to lzero; suc to lsuc)

data ⊥ : Set where

record ⊤ : Set where
  constructor tt

data ℕ : Set where
  zero : ℕ
  suc  : ℕ → ℕ

module Inductive where
  data List (A : Set) : Set where
    [] : List A
    _∷_ : A → List A → List A

data Bool : Set where
  true false : Bool

record Σ {a b} (A : Set a) (B : A → Set b) : Set (a ⊔ b) where
  constructor _,_
  field
    fst : A
    snd : B fst

∃ : ∀ {a b} {A : Set a} (B : A → Set b) → Set (a ⊔ b)
∃ {a} {b} {A} B = Σ A B

if : ∀ {p} {P : Bool → Set p} → ∀ b → P true → P false → P b
if true  t e = t
if false t e = e

_⊎_ : (A B : Set) → Set
A ⊎ B = ∃ λ b → if b A B

inj₁ : {A B : Set} → A → A ⊎ B
inj₁ x = true , x

inj₂ : {A B : Set} → B → A ⊎ B
inj₂ x = false , x

⊎-elim : ∀ {p} {A B : Set} {P : A ⊎ B → Set p} →
  (∀ x → P (inj₁ x)) → (∀ y → P (inj₂ y)) → ∀ s → P s
⊎-elim x y (true  , snd) = x snd
⊎-elim x y (false , snd) = y snd

_×_ : (A B : Set) → Set
A × B = ∀ b → if b A B

proj₁ : {A B : Set} → A × B → A
proj₁ x = x true

proj₂ : {A B : Set} → A × B → B
proj₂ x = x false

Fin : ℕ → Set
Fin zero    = ⊥
Fin (suc n) = ⊤ ⊎ Fin n

Vec : Set → ℕ → Set
Vec A n = Fin n → A

module VecList where
  List : Set → Set
  List A = ∃ λ n → Vec A n
