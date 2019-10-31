{-# OPTIONS --without-K --safe #-}

-- https://personal.cis.strath.ac.uk/conor.mcbride/pub/DepRep/DepRep.pdf

module Experiment.Outrageous.#03 where

open import Experiment.Outrageous.#02

data U : Set
El : U → Set

data U where
  :Zero: :𝟏: :𝟐: :ℕ: : U
  :Π: :Σ: : (S : U) → (El S → U) → U
El :Zero: = Zero
El :𝟏:    = 𝟏
El :𝟐:    = 𝟐
El :ℕ:    = ℕ
El (:Π: S T) = (s : El S) → El (T s)
El (:Σ: S T) = Σ (El S) λ s → El (T s)

_:→:_ : U → U → U
S :→: T = :Π: S λ _ → T

_:×:_ : U → U → U
S :×: T = :Σ: S λ _ → T

:If: : 𝟐 → U → U → U
:If: tt T F = T
:If: ff T F = F

:Vec: : U → ℕ → U
:Vec: X ze     = :𝟏:
:Vec: X (su n) = X :×: :Vec: X n
