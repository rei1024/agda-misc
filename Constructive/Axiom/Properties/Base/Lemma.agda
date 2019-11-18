-- Lemma for `Constructive.Axiom.Properties.Base`

{-# OPTIONS --without-K --safe #-}

module Constructive.Axiom.Properties.Base.Lemma where

-- agda-stdlib
open import Data.Empty
open import Data.Nat
import Data.Nat.Properties as ℕₚ
open import Data.Product
open import Data.Sum as Sum
open import Data.Sum.Properties
open import Function.Base
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary

-- agda-misc
open import Constructive.Combinators
open import Constructive.Common


-- lemma for `ℕ-llpo⇒mp∨`
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

private
  1+n≰0 : ∀ n → ¬ (suc n ≤ 0)
  1+n≰0 n ()

module _ {p} {P : ℕ → Set p} (P? : DecU P) where
  ℕ<-any-dec : DecU (λ n → ∃ λ m → m < n × P m)
  ℕ<-any-dec zero           = inj₂ λ {(m , m<0 , _) → 1+n≰0 m m<0}
  ℕ<-any-dec (suc n) with ℕ≤-any-dec P? n
  ... | inj₁ (m , m≤n , Pm) = inj₁ (m , s≤s m≤n , Pm)
  ... | inj₂ ¬∃m→m≤n×Pm     = inj₂ (contraposition f ¬∃m→m≤n×Pm)
    where
    f : (∃ λ m → suc m ≤ suc n × P m) → ∃ λ m → m ≤ n × P m
    f (m , sm≤sn , Pm) = m , (ℕₚ.≤-pred sm≤sn , Pm)

  ℕ≤-all-dec : DecU (λ n → ∀ m → m ≤ n → P m)
  ℕ≤-all-dec n with ℕ≤-any-dec (¬-DecU P?) n
  ... | inj₁ (m , m≤n , ¬Pm) = inj₂ λ ∀i→i≤n→Pi → ¬Pm (∀i→i≤n→Pi m m≤n)
  ... | inj₂ ¬∃m→m≤n×¬Pm     =
    inj₁ λ m m≤n → DecU⇒stable P? m λ ¬Pm → ¬∃m→m≤n×¬Pm (m , m≤n , ¬Pm)

module _ {p} {P : ℕ → Set p} (P? : DecU P) where
  ℕ<-all-dec : DecU (λ n → ∀ m → m < n → P m)
  ℕ<-all-dec n with ℕ<-any-dec (¬-DecU P?) n
  ... | inj₁ (m , m<n , ¬Pm) = inj₂ λ ∀i→i<n→Pi → ¬Pm (∀i→i<n→Pi m m<n)
  ... | inj₂ ¬∃m→m<n×¬Pm     =
    inj₁ λ m m<n → DecU⇒stable P? m λ ¬Pm → ¬∃m→m<n×¬Pm (m , m<n , ¬Pm)

-- lemma for llpo-ℕ⇒llpo
lemma₁ : ∀ {p} {P : ℕ → Set p} →
         (∀ m n → m ≢ n → P m ⊎ P n) →
         ∃ (λ n → ¬ P (2 * n)) → ∃ (λ n → ¬ P (suc (2 * n))) → ⊥
lemma₁ ∀mn→m≢n→Pm⊎Pn (m , ¬P2m) (n , ¬P1+2n) with
  ∀mn→m≢n→Pm⊎Pn (2 * m) (suc (2 * n)) (ℕₚ.even≢odd m n)
... | inj₁ P2m   = ¬P2m P2m
... | inj₂ P1+2n = ¬P1+2n P1+2n

parity : ℕ → ℕ ⊎ ℕ
parity zero          = inj₁ zero
parity (suc zero)    = inj₂ zero
parity (suc (suc n)) = Sum.map suc suc (parity n)

parity-even : ∀ n → parity (2 * n) ≡ inj₁ n
parity-even zero    = refl
parity-even (suc n) = begin
  parity (2 * (suc n))             ≡⟨ cong parity (ℕₚ.*-distribˡ-+ 2 1 n) ⟩
  parity (2 + 2 * n)               ≡⟨⟩
  Sum.map suc suc (parity (2 * n)) ≡⟨ cong (Sum.map suc suc) (parity-even n) ⟩
  Sum.map suc suc (inj₁ n)         ≡⟨⟩
  inj₁ (suc n)                     ∎
  where open ≡-Reasoning

parity-odd : ∀ n → parity (suc (2 * n)) ≡ inj₂ n
parity-odd zero    = refl
parity-odd (suc n) = begin
  parity (suc (2 * suc n))             ≡⟨ cong (parity ∘ suc) $ ℕₚ.*-distribˡ-+ 2 1 n ⟩
  parity (1 + (2 * 1 + 2 * n))         ≡⟨⟩
  parity (2 + (1 + 2 * n))             ≡⟨⟩
  Sum.map suc suc (parity (1 + 2 * n)) ≡⟨ cong (Sum.map suc suc) (parity-odd n) ⟩
  Sum.map suc suc (inj₂ n)             ≡⟨⟩
  inj₂ (suc n)                         ∎
  where open ≡-Reasoning

Sum-map-injective : ∀ {a b c d} {A : Set a} {B : Set b} {C : Set c} {D : Set d}
                    {f : A → C} {g : B → D} →
                    (∀ {u v} → f u ≡ f v → u ≡ v) →
                    (∀ {u v} → g u ≡ g v → u ≡ v) → ∀ {x y} →
                    Sum.map f g x ≡ Sum.map f g y → x ≡ y
Sum-map-injective f-inj g-inj {inj₁ x} {inj₁ x₁} eq = cong inj₁ (f-inj (inj₁-injective eq))
Sum-map-injective f-ing g-inj {inj₂ y} {inj₂ y₁} eq = cong inj₂ (g-inj (inj₂-injective eq))

parity-injective : ∀ {m n} → parity m ≡ parity n → m ≡ n
parity-injective {zero}        {zero}        pm≡pn = refl
parity-injective {zero}        {suc (suc n)} pm≡pn with parity n
parity-injective {zero}        {suc (suc n)} () | inj₁ _
parity-injective {zero}        {suc (suc n)} () | inj₂ _
parity-injective {suc (suc m)} {zero}        pm≡pn with parity m
parity-injective {suc (suc m)} {zero}        () | inj₁ _
parity-injective {suc (suc m)} {zero}        () | inj₂ _
parity-injective {suc zero}    {suc zero}    pm≡pn = refl
parity-injective {suc zero}    {suc (suc n)} pm≡pn with parity n
parity-injective {suc zero}    {suc (suc n)} () | inj₁ _
parity-injective {suc zero}    {suc (suc n)} () | inj₂ _
parity-injective {suc (suc m)} {suc zero}    pm≡pn with parity m
parity-injective {suc (suc m)} {suc zero}    () | inj₁ _
parity-injective {suc (suc m)} {suc zero}    () | inj₂ _
parity-injective {suc (suc m)} {suc (suc n)} pm≡pn =
  cong (suc ∘ suc)
       (parity-injective
          (Sum-map-injective ℕₚ.suc-injective ℕₚ.suc-injective pm≡pn))

parity-even′ : ∀ {m n} → parity m ≡ inj₁ n → m ≡ 2 * n
parity-even′ {m} {n} eq = parity-injective (begin
    parity m       ≡⟨ eq ⟩
    inj₁ n         ≡⟨ sym $ parity-even n ⟩
    parity (2 * n) ∎)
  where open ≡-Reasoning

parity-odd′ : ∀ {m n} → parity m ≡ inj₂ n → m ≡ 1 + 2 * n
parity-odd′ {m} {n} eq = parity-injective (begin
  parity m           ≡⟨ eq ⟩
  inj₂ n             ≡⟨ sym $ parity-odd n ⟩
  parity (1 + 2 * n) ∎)
  where open ≡-Reasoning

mix : ℕ ⊎ ℕ → ℕ
mix = Sum.[ (λ n → 2 * n) , (λ n → 1 + 2 * n) ]

parity-mix : ∀ s → parity (mix s) ≡ s
parity-mix (inj₁ n) = parity-even n
parity-mix (inj₂ n) = parity-odd n

mix-parity : ∀ n → mix (parity n) ≡ n
mix-parity n = parity-injective (parity-mix (parity n))
