{-# OPTIONS --without-K --safe #-}

module Experiment.Zero where

open import Level using (_⊔_)

-- Empty type
data ⊥ : Set where

-- Unit type
record ⊤ : Set where
  constructor tt

-- Boolean
data Bool : Set where
  true false : Bool

-- Natural number
data ℕ : Set where
  zero : ℕ
  suc  : ℕ → ℕ

-- Propositional Equality
data _≡_ {a} {A : Set a} (x : A) : A → Set a where
  refl : x ≡ x

-- Sum type
data _⊎_ {a} {b} (A : Set a) (B : Set b) : Set (a ⊔ b) where
  inj₁ : A → A ⊎ B
  inj₂ : B → A ⊎ B

-- Dependent Product type
record Σ {a} {b} (A : Set a) (B : A → Set b) : Set (a ⊔ b) where
  constructor _,_
  field
    fst : A
    snd : B fst

-- Induction
⊤-ind : ∀ {p} {P : ⊤ → Set p} → P tt → ∀ x → P x
⊤-ind P⊤ tt = P⊤

⊥-ind : ∀ {p} {P : ⊥ → Set p} → ∀ x → P x
⊥-ind ()

Bool-ind : ∀ {p} {P : Bool → Set p} → P true → P false → ∀ x → P x
Bool-ind t e true  = t
Bool-ind t e false = e

ℕ-ind : ∀ {p} {P : ℕ → Set p} → P zero → (∀ m → P m → P (suc m)) → ∀ n → P n
ℕ-ind P0 Ps zero    = P0
ℕ-ind P0 Ps (suc n) = Ps n (ℕ-ind P0 Ps n)

≡-ind : ∀ {a p} {A : Set a}
        (P : (x y : A) → x ≡ y → Set p) →
        (∀ x → P x x refl) →
        ∀ x y (eq : x ≡ y) → P x y eq
≡-ind P Pr x .x refl = Pr x

⊎-ind : ∀ {a b p} {A : Set a} {B : Set b} {P : A ⊎ B → Set p} →
        (∀ x → P (inj₁ x)) → (∀ y → P (inj₂ y)) → ∀ s → P s
⊎-ind i1 i2 (inj₁ x) = i1 x
⊎-ind i1 i2 (inj₂ y) = i2 y

Σ-ind : ∀ {a b p} {A : Set a} {B : A → Set b} {P : Σ A B → Set p} →
        (∀ x y → P (x , y)) → ∀ p → P p
Σ-ind f (x , y) = f x y
