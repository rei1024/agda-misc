{-# OPTIONS --without-K --safe #-}

module Experiment.FingerTree where
open import Level renaming (zero to lzero ; suc to lsuc)
open import Algebra

open import Experiment.FingerTree.Common

data Digit {a} (A : Set a) : Set a where
  one   : (a       : A) → Digit A
  two   : (a b     : A) → Digit A
  three : (a b c   : A) → Digit A
  four  : (a b c d : A) → Digit A

data Node {v a} (V : Set v) (A : Set a) : Set (a ⊔ v) where
  :node2 : (v : V) → (a b   : A) → Node V A
  :node3 : (v : V) → (a b c : A) → Node V A

nodeToDigit : ∀ {v a} {V : Set v} {A : Set a} → Node V A → Digit A
nodeToDigit (:node2 v a b  ) = two a b
nodeToDigit (:node3 v a b c) = three a b c

data FingerTree {v a} (V : Set v) (A : Set a) : Set (a ⊔ v) where
  :empty  : FingerTree V A
  :single : A → FingerTree V A
  :deep   : V → Digit A → FingerTree V (Node V A) → Digit A → FingerTree V A

Digit-foldr : ∀ {a b} {A : Set a} {B : Set b} → (A → B → B) → B → Digit A → B
Digit-foldr _<>_ e (one   a)       = a <> e
Digit-foldr _<>_ e (two   a b)     = a <> (b <> e)
Digit-foldr _<>_ e (three a b c)   = a <> (b <> (c <> e))
Digit-foldr _<>_ e (four  a b c d) = a <> (b <> (c <> (d <> e)))

Node-foldr : ∀ {v a b} {V : Set v} {A : Set a} {B : Set b} →
  (A → B → B) → B → Node V A → B
Node-foldr _<>_ e (:node2 v a b  ) = a <> (b <> e)
Node-foldr _<>_ e (:node3 v a b c) = a <> (b <> (c <> e))

Node-measure : ∀ {v a} {V : Set v} {A : Set a} → Node V A → V
Node-measure (:node2 v a b  ) = v
Node-measure (:node3 v a b c) = v

record IsMeasured {c e a} (M : Monoid c e) (A : Set a) : Set (a ⊔ c ⊔ e) where
  open Monoid M
  field
    measure : A → Carrier

module Constructor {c e a} {A : Set a} {M : Monoid c e} (MS : IsMeasured M A) where
  open Monoid M renaming (Carrier to V)
  open IsMeasured MS

  empty : FingerTree V A
  empty = :empty

  single : A → FingerTree V A
  single = :single

  deep : Digit A → FingerTree V (Node V A) → Digit A → FingerTree V A
  deep pr m sf = :deep {! (Node-measure pr ∙ measure m) ∙ Node-measure sf  !} pr m sf
