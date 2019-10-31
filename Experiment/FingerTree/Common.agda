{-# OPTIONS --without-K --safe #-}

module Experiment.FingerTree.Common where
open import Level renaming (zero to lzero ; suc to lsuc)
open import Algebra
open import Data.Product
open import Function.Core
open import Function.Endomorphism.Propositional
open import Data.Nat hiding (_⊔_)
import Data.Nat.Properties as ℕₚ

foldr-to-foldMap : ∀ {a b e} {F : Set a → Set a} →
 (∀ {A : Set a} {B : Set b} → (A → B → B) → B → F A → B) →
 ∀ {A : Set a} (M : Monoid b e) → (A → Monoid.Carrier M) → F A → Monoid.Carrier M
foldr-to-foldMap foldr M f xs = foldr (λ x m → Monoid._∙_ M (f x) m) (Monoid.ε M) xs

foldMap-to-foldr : ∀ {a b} {F : Set a → Set a} →
  (∀ {A : Set a} (M : Monoid b b) → (A → Monoid.Carrier M) → F A → Monoid.Carrier M) →
  ∀ {A : Set a} {B : Set b} → (A → B → B) → B → F A → B
foldMap-to-foldr foldMap {B = B} f e xs = foldMap (∘-id-monoid B) f xs e

dual : ∀ {c e} → Monoid c e → Monoid c e
dual m = record
  { Carrier = Carrier
  ; _≈_      = _≈_
  ; _∙_      = flip _∙_
  ; ε        = ε
  ; isMonoid = record
    { isSemigroup = record
      { isMagma = record
        { isEquivalence = isEquivalence
        ; ∙-cong        = λ x≈y u≈v → ∙-cong u≈v x≈y
        }
      ; assoc   = λ x y z → sym $ assoc z y x
      }
    ; identity    = identityʳ , identityˡ
    }
  }
  where open Monoid m

foldMap-to-foldl : ∀ {a b} {F : Set a → Set a} →
  (∀ {A : Set a} (M : Monoid b b) → (A → Monoid.Carrier M) → F A → Monoid.Carrier M) →
  ∀ {A : Set a} {B : Set b} → (B → A → B) → B → F A → B
foldMap-to-foldl foldMap {B = B} f e xs = foldMap (dual (∘-id-monoid B)) (flip f) xs e

record RawFoldable {a} (F : Set a → Set a) : Set (lsuc a) where
  field
    foldMap : ∀ {A : Set a} (M : Monoid a a) → (A → Monoid.Carrier M) → F A → Monoid.Carrier M

  fold : (M : Monoid a a) → F (Monoid.Carrier M) → Monoid.Carrier M
  fold M = foldMap M id

  foldr : ∀ {A B : Set a} → (A → B → B) → B → F A → B
  foldr {A} {B} f e xs = foldMap (∘-id-monoid B) f xs e

  foldl : ∀ {A B : Set a} → (B → A → B) → B → F A → B
  foldl {A} {B} f e xs = foldMap (dual (∘-id-monoid B)) (flip f) xs e

fromFoldr : ∀ {a} {F : Set a → Set a} →
  (∀ {A B : Set a} → (A → B → B) → B → F A → B) → RawFoldable {a} F
fromFoldr foldr = record
  { foldMap = foldr-to-foldMap foldr
  }
