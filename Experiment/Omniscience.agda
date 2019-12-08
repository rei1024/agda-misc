{-# OPTIONS --without-K --safe --exact-split #-}

module Experiment.Omniscience where

open import Level using () renaming (zero to lzero)
open import Data.Nat using (ℕ; zero; suc; _≤_; _+_)
open import Data.Nat.Properties using (≤-refl; +-identityʳ)
open import Data.Product using (Σ; _,_; proj₁; proj₂; ∃; _×_)
open import Data.Bool using (Bool; true; false; _∧_; not)
open import Data.Bool.Properties using (∧-assoc; ∧-idem)
open import Function.Base using (_$_)
open import Relation.Binary using (Rel)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; subst; sym; _≢_; cong; module ≡-Reasoning)

infix 5 _≤ᵇ_

_≤ᵇ_ : Bool → Bool → Bool
false ≤ᵇ false = true
true  ≤ᵇ false = false
false ≤ᵇ true  = true
true  ≤ᵇ true  = true

x≤ᵇtrue≡true : ∀ x → x ≤ᵇ true ≡ true
x≤ᵇtrue≡true false = refl
x≤ᵇtrue≡true true  = refl

Decrease : (ℕ → Bool) → Set
Decrease α = ∀ i → α (suc i) ≤ᵇ α i ≡ true

ℕ∞ : Set
ℕ∞ = Σ (ℕ → Bool) Decrease

-- less n i ≡ true <=> n > i
less : ℕ → ℕ → Bool
less zero    zero    = false
less zero    (suc n) = false
less (suc m) zero    = true
less (suc m) (suc n) = less m n

less-decrease : ∀ n → Decrease (less n)
less-decrease zero     zero   = refl
less-decrease zero    (suc i) = refl
less-decrease (suc n) zero    = x≤ᵇtrue≡true (less n 0)
less-decrease (suc n) (suc i) = less-decrease n i

toℕ∞ : ℕ → ℕ∞
toℕ∞ n = less n , less-decrease n

_≈C_ : Rel (ℕ → Bool) lzero
α ≈C β = ∀ i → α i ≡ β i

_≈_ : Rel ℕ∞ lzero
x ≈ y = proj₁ x ≈C proj₁ y

_#C_ : Rel (ℕ → Bool) lzero
α #C β = ∃ λ i → α i ≢ β i

_#_ : Rel ℕ∞ lzero
x # y = proj₁ x #C proj₁ y

-- retract
𝓇 : (ℕ → Bool) → (ℕ → Bool)
𝓇 α zero    = α 0
𝓇 α (suc n) = α (suc n) ∧ 𝓇 α n

𝓇-decrease : ∀ α → Decrease (𝓇 α)
𝓇-decrease α i = lemma (α (suc i)) (𝓇 α i)
  where
  lemma : ∀ x y → x ∧ y ≤ᵇ y ≡ true
  lemma false false = refl
  lemma false true  = refl
  lemma true  false = refl
  lemma true  true  = refl

𝓇-idem : ∀ α → 𝓇 (𝓇 α) ≈C 𝓇 α
𝓇-idem α zero    = refl
𝓇-idem α (suc i) = begin
  (α (suc i) ∧ 𝓇 α i) ∧ 𝓇 (𝓇 α) i
    ≡⟨ cong (λ v → (α (suc i) ∧ 𝓇 α i) ∧ v) $ 𝓇-idem α i ⟩
  (α (suc i) ∧ 𝓇 α i) ∧ 𝓇 α i
    ≡⟨ ∧-assoc (α (suc i)) (𝓇 α i) (𝓇 α i) ⟩
  α (suc i) ∧ (𝓇 α i ∧ 𝓇 α i)
    ≡⟨ cong (λ v → α (suc i) ∧ v) $ ∧-idem (𝓇 α i) ⟩
  α (suc i) ∧ 𝓇 α i ∎
  where open ≡-Reasoning

⟦_⟧ : ℕ∞ → (ℕ → Bool)
⟦_⟧ = proj₁

private
  contraposition-Bool : ∀ {x y z} → (x ≡ z → y ≡ z) → y ≡ not z → x ≡ not z
  contraposition-Bool {false} {false} {true} f e = refl
  contraposition-Bool {false} {true} {false} f e = (λ ()) $ f refl
  contraposition-Bool {true}  {false} {true} f e = (λ ()) $ f refl
  contraposition-Bool {true}  {true} {false} f e = refl

  ≤ᵇ-to-fun : ∀ {x y} → x ≤ᵇ y ≡ true → x ≡ true → y ≡ true
  ≤ᵇ-to-fun {true} {true} _ _ = refl

lemma-3-2-lemma : ∀ (x : ℕ∞) m n → ⟦ x ⟧ n ≡ false → ⟦ x ⟧ (m + n) ≡ false
lemma-3-2-lemma x@(α , d) zero    n αn≡false = αn≡false
lemma-3-2-lemma x@(α , d) (suc m) n αn≡false =
  contraposition-Bool (≤ᵇ-to-fun (d (m + n))) (lemma-3-2-lemma x m n αn≡false)

lemma-3-2 : ∀ (x : ℕ∞) n → ⟦ x ⟧ n ≡ false → ∃ λ k → k ≤ n × x ≈ toℕ∞ k
lemma-3-2 x@(α , d) zero    αn≡false = 0 , (≤-refl , f)
  where
  f : ∀ i → α i ≡ less 0 i
  f zero    = αn≡false
  f (suc i) = subst (λ v → α (suc v) ≡ false) (+-identityʳ i) $
                lemma-3-2-lemma x (suc i) 0 αn≡false
lemma-3-2 (α , d) (suc n) αn≡false = {!   !}

-- α i ≡ less 0 i
