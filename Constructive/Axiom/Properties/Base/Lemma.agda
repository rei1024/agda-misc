-- Lemma for `Constructive.Axiom.Properties.Base`

{-# OPTIONS --without-K --safe #-}

module Constructive.Axiom.Properties.Base.Lemma where

-- agda-stdlib
open import Data.Empty
open import Data.Nat
import Data.Nat.Properties as ℕₚ
open import Data.Product
open import Data.Sum
open import Function.Base
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary

-- agda-misc
open import Constructive.Combinators
open import Constructive.Common


-- lemma for `ℕ-llpo⇒mp∨`
private
  1+n≰0 : ∀ n → ¬ (suc n ≤ 0)
  1+n≰0 n ()

ℕ≤-any-dec : ∀ {p} {P : ℕ → Set p} → DecU P → DecU (λ n → ∃ λ m → m ≤ n × P m)
ℕ≤-any-dec {P = P} P? zero with P? 0
... | inj₁  P0 = inj₁ (0 , ℕₚ.≤-refl , P0)
... | inj₂ ¬P0 = inj₂ λ {(m , m≤0 , Pm) → ¬P0 (subst P (ℕₚ.n≤0⇒n≡0 m≤0) Pm)}
ℕ≤-any-dec P? (suc n) with P? 0
... | inj₁  P0 = inj₁ (0 , (z≤n , P0))
... | inj₂ ¬P0 with ℕ≤-any-dec (P? ∘ suc) n
ℕ≤-any-dec {P = P} P? (suc n) | inj₂ ¬P0 | inj₁ (m , m≤n , Psm) =
  inj₁ (suc m , s≤s m≤n , Psm)
ℕ≤-any-dec {P = P} P? (suc n) | inj₂ ¬P0 | inj₂ ¬∃m→m≤n×Psm     = inj₂ f
  where
  f : (∃ λ m → m ≤ suc n × P m) → ⊥
  f (zero  , m≤sn  , Pm)  = ¬P0 Pm
  f (suc m , sm≤sn , Psm) = ¬∃m→m≤n×Psm (m , (ℕₚ.≤-pred sm≤sn , Psm))

ℕ<-any-dec : ∀ {p} {P : ℕ → Set p} → DecU P →
             DecU (λ n → ∃ λ m → m < n × P m)
ℕ<-any-dec P? zero     = inj₂ λ {(m , m<0 , _) → 1+n≰0 m m<0}
ℕ<-any-dec {P = P} P? (suc n) with ℕ≤-any-dec P? n
... | inj₁ (m , m≤n , Pm) = inj₁ (m , s≤s m≤n , Pm)
... | inj₂ ¬∃m→m≤n×Pm     = inj₂ (contraposition f ¬∃m→m≤n×Pm)
  where
  f : (∃ λ m → suc m ≤ suc n × P m) → ∃ λ m → m ≤ n × P m
  f (m , sm≤sn , Pm) = m , (ℕₚ.≤-pred sm≤sn , Pm)
