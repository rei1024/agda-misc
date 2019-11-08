-- "Ordinal notations via simultaneous definitions"

module Experiment.Ord where

open import Level renaming (zero to lzero; suc to lsuc)
open import Relation.Binary
open import Relation.Binary.PropositionalEquality
open import Data.Sum

data Ord : Set
data _<_ : Rel Ord lzero
_≥_ : Rel Ord lzero
fst : Ord → Ord
data Ord where
  𝟎 : Ord
  ω^_+_[_] : (a b : Ord) → a ≥ fst b → Ord
data _<_ where
  <₁ : {a : Ord} → a ≢ 𝟎 → 𝟎 < a
  <₂ : {a b c d : Ord} (r : a ≥ fst c) (s : b ≥ fst d) →
       a < b → ω^ a + c [ r ] < ω^ b + d [ s ]
  <₃ : {a b c : Ord} → (r : a ≥ fst b) (s : a ≥ fst c) → b < c → ω^ a + b [ r ] < ω^ a + c [ s ]
fst 𝟎                = 𝟎
fst (ω^ α + _ [ _ ]) = α
a ≥ b = (b < a) ⊎ (a ≡ b)

_+_ : Ord → Ord → Ord
𝟎 + b = b
a@(ω^ _ + _ [ _ ]) + 𝟎 = a
ω^ a + c [ r ] + ω^ b + d [ s ] = {!   !}

_*_ : Ord → Ord → Ord
a * b = {!   !}
