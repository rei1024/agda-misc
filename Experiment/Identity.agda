{-# OPTIONS --without-K --safe #-}
module Experiment.Identity where

open import Level renaming (zero to lzero; suc to lsuc)
open import Relation.Binary.PropositionalEquality as P using (refl; _≡_)
  renaming (trans to ≡-trans; sym to ≡-sym; cong to ≡-cong)
import Relation.Binary.Reasoning.Setoid as SetoidReasoning
open import Relation.Binary

record JBundle a : Set (lsuc a) where
  field
    Carrier : Set a
    _≈_     : Rel Carrier a
    ≈-refl  : ∀ {x} → x ≈ x
    J       : (C : ∀ x y → x ≈ y → Set a) → (∀ x → C x x ≈-refl) →
              ∀ x y (p : x ≈ y) → C x y p
    J-β     : ∀ (C : ∀ x y → x ≈ y → Set a) (c : ∀ x → C x x ≈-refl) x →
              J C c x x ≈-refl ≡ c x

module JBundleProperties {a} (jBundle : JBundle a) where
  open JBundle jBundle renaming (Carrier to A)
  sym : ∀ {x y} → x ≈ y → y ≈ x
  sym {x} {y} x≈y = J (λ x₁ y₁ x₁≈y₁ → y₁ ≈ x₁) (λ _ → ≈-refl) x y x≈y

  sym-≈-refl : ∀ x → sym (≈-refl {x}) ≡ ≈-refl
  sym-≈-refl x = J-β (λ x₁ y₁ x₁≈y₁ → y₁ ≈ x₁) (λ _ → ≈-refl) x

  sym-involutive : ∀ {x y} (p : x ≈ y) → sym (sym p) ≡ p
  sym-involutive {x} {y} p =
   J (λ x₁ y₁ x₁≈y₁ → sym (sym x₁≈y₁) ≡ x₁≈y₁)
     (λ z → ≡-trans (≡-cong sym (sym-≈-refl z)) (sym-≈-refl z)) x y p

  sym-injective : ∀ {x y} {p q : x ≈ y} → sym p ≡ sym q → p ≡ q
  sym-injective {p = p} {q} eq = begin
    p           ≡⟨ ≡-sym (sym-involutive p) ⟩
    sym (sym p) ≡⟨ ≡-cong sym eq ⟩
    sym (sym q) ≡⟨ sym-involutive q ⟩
    q           ∎
    where open P.≡-Reasoning

  trans : ∀ {x y z} → x ≈ y → y ≈ z → x ≈ z
  trans {x} {y} {z} x≈y y≈z = J D (λ u → λ w q → q) x y x≈y z y≈z
    where
    D : ∀ u v → u ≈ v → Set _
    D u v u≈v = ∀ w → (q : v ≈ w) → u ≈ w
