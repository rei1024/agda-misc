{-# OPTIONS --without-K --safe #-}

-- https://personal.cis.strath.ac.uk/conor.mcbride/pub/DepRep/DepRep.pdf

module Experiment.Outrageous.#02 where

data Zero : Set where
magic : Zero → (X : Set) → X
magic ()
record 𝟏 : Set where
  constructor void
data 𝟐 : Set where
  tt : 𝟐
  ff : 𝟐
If : 𝟐 → Set → Set → Set
If tt T F = T
If ff T F = F
if : (b : 𝟐) → (P : 𝟐 → Set) → P tt → P ff → P b
if tt P t f = t
if ff P t f = f
data ℕ : Set where
  ze : ℕ
  su : ℕ → ℕ
rec : (n : ℕ) → (P : ℕ → Set) → P ze → ((n : ℕ) → P n → P (su n)) → P n
rec ze     P z s = z
rec (su n) P z s = s n (rec n P z s)
record Σ (S : Set) (T : S → Set) : Set where
  constructor _,_
  field
    fst : S
    snd : T fst
