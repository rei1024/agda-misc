module TypeTheory.Nat.AnotherMono.Structure where

open import Level renaming (zero to lzero; suc to lsuc)
open import Data.Empty using (⊥)
open import Data.Product using (Σ; _×_; _,_)
open import Relation.Binary using (Rel)
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary using (¬_)

record Nat : Set₁ where
  field
    N        : Set
    zero     : N
    suc      : N → N
    ind      : (P : N → Set) → P zero → (∀ k → P k → P (suc k)) → ∀ n → P n
    ind-zero : ∀ P P-zero P-suc → ind P P-zero P-suc zero ≡ P-zero
    ind-suc  : ∀ P P-zero P-suc n → ind P P-zero P-suc (suc n) ≡
                                    P-suc n (ind P P-zero P-suc n)
    s≢z      : ∀ {n} → suc n ≢ zero

  0N : N
  0N = zero

  1N : N
  1N = suc zero

  z≢s : ∀ {n} → zero ≢ suc n
  z≢s = ≢-sym s≢z

  rec : {A : Set} → A → (A → A) → N → A
  rec {A} z s = ind (λ _ → A) z (λ _ → s)

  rec-zero : ∀ {A} (z : A) s → rec z s zero ≡ z
  rec-zero z s = ind-zero _ _ _

  rec-suc : ∀ {A} (z : A) s n → rec z s (suc n) ≡ s (rec z s n)
  rec-suc z s n = ind-suc _ _ _ _

  infixl 6 _+_
  infixl 7 _*_
  infix 4 _≤_ _<_ _≥_ _>_ _≰_

  -- Arithematic
  -- Addition
  _+_ : N → N → N
  m + n = rec n suc m

  -- Multiplication
  _*_ : N → N → N
  m * n = rec zero (n +_) m

  -- Order
  _≤_ : Rel N lzero
  m ≤ n = Σ N λ o → o + m ≡ n

  _<_ : Rel N lzero
  m < n = suc m ≤ n

  _≥_ : Rel N lzero
  m ≥ n = n ≤ m

  _>_ : Rel N lzero
  m > n = n < m

  _≰_ : Rel N lzero
  m ≰ n = ¬ m ≤ n

  _≮_ : Rel N lzero
  m ≮ n = ¬ m < n

  _≱_ : Rel N lzero
  m ≱ n = ¬ m ≥ n

  _≯_ : Rel N lzero
  m ≯ n = ¬ m > n
