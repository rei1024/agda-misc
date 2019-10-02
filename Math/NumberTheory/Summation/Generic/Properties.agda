{-# OPTIONS --without-K --safe #-}

module Math.NumberTheory.Summation.Generic.Properties where

-- agda-stdlib
open import Algebra
import Algebra.Operations.CommutativeMonoid as CommutativeMonoidOperations
open import Data.Nat as ℕ hiding (_+_; _*_)
import Data.Nat.Properties as ℕₚ
open import Relation.Binary.PropositionalEquality as ≡ using (_≡_)
import Relation.Binary.Reasoning.Setoid as SetoidReasoning
open import Function.Core

-- agda-misc
open import Math.NumberTheory.Summation.Generic

module MonoidSummationProperties {c e} (M : Monoid c e) where
  open MonoidSummation M
  open Monoid M
  open SetoidReasoning setoid

  Σ<-cong : ∀ {f g m n} → (∀ x → f x ≈ g x) → m ≡ n → Σ< f m ≈ Σ< g n
  Σ<-cong {f} {g} {0}     {.0}       f≈g ≡.refl = refl
  Σ<-cong {f} {g} {suc m} {.(suc m)} f≈g ≡.refl = begin
    f m ∙ Σ< f m ≈⟨ ∙-cong (f≈g m) (Σ<-cong {m = m} {n = m} f≈g ≡.refl) ⟩
    g m ∙ Σ< g m ∎

  Σ<-congˡ : ∀ f {m n} → m ≡ n → Σ< f m ≈ Σ< f n
  Σ<-congˡ f = Σ<-cong (λ _ → refl)

  Σ<-congʳ : ∀ {f g} n → (∀ x → f x ≈ g x) → Σ< f n ≈ Σ< g n
  Σ<-congʳ n f≈g = Σ<-cong {m = n} f≈g ≡.refl

  Σ≤-cong : ∀ {f g m n} → (∀ x → f x ≈ g x) → m ≡ n → Σ≤ f m ≈ Σ≤ g n
  Σ≤-cong f≈g m≡n = Σ<-cong f≈g (≡.cong suc m≡n)

  Σ≤-congˡ : ∀ f {m n} → m ≡ n → Σ≤ f m ≈ Σ≤ f n
  Σ≤-congˡ f m≡n = Σ<-congˡ f (≡.cong suc m≡n)

  Σ≤-congʳ : ∀ {f g} n → (∀ x → f x ≈ g x) → Σ≤ f n ≈ Σ≤ g n
  Σ≤-congʳ n = Σ<-congʳ (suc n)

  Σ<range-cong : ∀ {f g : ℕ → Carrier} {m n o p} →
    (∀ x → f x ≈ g x) → m ≡ n → o ≡ p → Σ<range f m o ≈ Σ<range g n p
  Σ<range-cong {f} {g} {m} {.m} {o} {.o} f≈g ≡.refl ≡.refl = begin
    Σ< (λ k → f (m ℕ.+ k)) (o ∸ m) ≈⟨ Σ<-congʳ (o ∸ m) (λ x → f≈g (m ℕ.+ x)) ⟩
    Σ< (λ k → g (m ℕ.+ k)) (o ∸ m) ∎

  Σ≤range-cong : ∀ {f g : ℕ → Carrier} {m n o p} →
    (∀ x → f x ≈ g x) → m ≡ n → o ≡ p → Σ≤range f m o ≈ Σ≤range g n p
  Σ≤range-cong f≈g m≡n o≡p = Σ<range-cong f≈g m≡n (≡.cong suc o≡p)

  Σ<-0 : ∀ n → Σ< (λ _ → ε) n ≈ ε
  Σ<-0 zero    = refl
  Σ<-0 (suc n) = begin
    ε ∙ Σ< (λ _ → ε) n ≈⟨ ∙-congˡ $ Σ<-0 n ⟩
    ε ∙ ε              ≈⟨ identityʳ ε ⟩
    ε                  ∎

  Σ≤-0 : ∀ n → Σ≤ (λ _ → ε) n ≈ ε
  Σ≤-0 n = Σ<-0 (suc n)

  Σ<[f,1]≈f[0] : ∀ f → Σ< f 1 ≈ f 0
  Σ<[f,1]≈f[0] f = identityʳ (f 0)

  Σ≤[f,0]≈f[0] : ∀ f → Σ≤ f 0 ≈ f 0
  Σ≤[f,0]≈f[0] f = Σ<[f,1]≈f[0] f

  Σ<range[f,n,n]≈0 : ∀ f n → Σ<range f n n ≈ ε
  Σ<range[f,n,n]≈0 f n = begin
    Σ< (λ k → f (n ℕ.+ k)) (n ∸ n) ≈⟨ Σ<-congˡ _ $ ℕₚ.n∸n≡0 n ⟩
    Σ< (λ k → f (n ℕ.+ k)) 0       ∎

  Σ<-+ : ∀ f m n → Σ< f (m ℕ.+ n) ≈ Σ< (λ k → f (n ℕ.+ k)) m ∙ Σ< f n
  Σ<-+ f zero    n = sym $ identityˡ (Σ< f n)
  Σ<-+ f (suc m) n = begin
    f (m ℕ.+ n) ∙ Σ< f (m ℕ.+ n)
      ≈⟨ ∙-congˡ $ Σ<-+ f m n ⟩
    f (m ℕ.+ n) ∙ (Σ< (λ k → f (n ℕ.+ k)) m ∙ Σ< f n)
      ≈⟨ sym $ assoc (f (m ℕ.+ n)) v (Σ< f n) ⟩
    f (m ℕ.+ n) ∙ v ∙ Σ< f n
      ≈⟨ ∙-congʳ $ ∙-congʳ $ reflexive (≡.cong f (ℕₚ.+-comm m n)) ⟩
    f (n ℕ.+ m) ∙ v ∙ Σ< f n
     ∎
     where v = Σ< (λ k → f (n ℕ.+ k)) m

  -- TODO Σ≤-+ : ∀ f m n → Σ≤ f (1 + m + n) ≈ Σ≤ (λ k → f (1 + n + k)) (1 + n + k) ∙ Σ≤ f n

  Σ<-push-suc : ∀ f n → Σ< f (suc n) ≈ Σ< (λ k → f (suc k)) n ∙ f 0
  Σ<-push-suc f n = begin
    Σ< f (suc n)                    ≈⟨ Σ<-congˡ f $ ℕₚ.+-comm 1 n ⟩
    Σ< f (n ℕ.+ 1)                    ≈⟨ Σ<-+ f n 1 ⟩
    Σ< (λ k → f (suc k)) n ∙ Σ< f 1 ≈⟨ ∙-congˡ $ Σ<[f,1]≈f[0] f ⟩
    Σ< (λ k → f (suc k)) n ∙ f 0    ∎

module CommutativeMonoidSummationProperties
  {c e} (CM : CommutativeMonoid c e) where
  open CommutativeMonoid CM
  open MonoidSummation monoid
  open MonoidSummationProperties monoid public
  open CommutativeMonoidOperations CM
  open SetoidReasoning setoid

  Σ<-const : ∀ x n → Σ< (const x) n ≈ n × x
  Σ<-const x zero    = refl
  Σ<-const x (suc n) = ∙-congˡ (Σ<-const x n)

  Σ≤-const : ∀ x n → Σ≤ (const x) n ≈ suc n × x
  Σ≤-const x n = Σ<-const x (suc n)

  private
    lemma : ∀ a b c d → a ∙ b ∙ (c ∙ d) ≈ a ∙ c ∙ (b ∙ d)
    lemma a b c d = begin
      (a ∙ b) ∙ (c ∙ d) ≈⟨ assoc a b (c ∙ d) ⟩
      a ∙ (b ∙ (c ∙ d)) ≈⟨ sym $ ∙-congˡ $ assoc b c d ⟩
      a ∙ ((b ∙ c) ∙ d) ≈⟨ ∙-congˡ $ ∙-congʳ $ comm b c ⟩
      a ∙ ((c ∙ b) ∙ d) ≈⟨ ∙-congˡ $ assoc c b d ⟩
      a ∙ (c ∙ (b ∙ d)) ≈⟨ sym $ assoc a c (b ∙ d) ⟩
      (a ∙ c) ∙ (b ∙ d) ∎

  Σ<-distrib-+ : ∀ f g n → Σ< (λ k → f k ∙ g k) n ≈ Σ< f n ∙ Σ< g n
  Σ<-distrib-+ f g zero    = sym $ identityʳ ε
  Σ<-distrib-+ f g (suc n) = begin
    f n ∙ g n ∙ Σ< (λ k → f k ∙ g k) n ≈⟨ ∙-congˡ $ Σ<-distrib-+ f g n ⟩
    f n ∙ g n ∙ (Σ< f n ∙ Σ< g n)      ≈⟨ lemma (f n) (g n) (Σ< f n) (Σ< g n) ⟩
    (f n ∙ Σ< f n) ∙ (g n ∙ Σ< g n)    ∎

  Σ≤-distrib-+ : ∀ f g n → Σ≤ (λ k → f k ∙ g k) n ≈ Σ≤ f n ∙ Σ≤ g n
  Σ≤-distrib-+ f g n = Σ<-distrib-+ f g (suc n)

  Σ<-comm : ∀ (f : ℕ → ℕ → Carrier) m n →
    Σ< (λ i → Σ< (λ j → f i j) n) m ≈ Σ< (λ j → Σ< (λ i → f i j) m) n
  Σ<-comm f zero    n = sym $ Σ<-0 n
  Σ<-comm f (suc m) n = begin
    Σ< (λ i → Σ< (f i) n) (suc m)
     ≈⟨ refl ⟩
    Σ< (f m) n ∙ Σ< (λ i → Σ< (f i) n) m
      ≈⟨ ∙-congˡ $ Σ<-comm f m n ⟩
    Σ< (λ j → f m j) n ∙ Σ< (λ j → Σ< (λ i → f i j) m) n
      ≈⟨ sym $ Σ<-distrib-+ (λ j → f m j) (λ j → Σ< (λ i → f i j) m) n ⟩
    Σ< (λ j → f m j ∙ Σ< (λ i → f i j) m) n
      ≈⟨ refl ⟩
    Σ< (λ j → Σ< (λ i → f i j) (suc m)) n
      ∎

  Σ≤-comm : ∀ (f : ℕ → ℕ → Carrier) m n →
    Σ≤ (λ i → Σ≤ (λ j → f i j) n) m ≈ Σ≤ (λ j → Σ≤ (λ i → f i j) m) n
  Σ≤-comm f m n = Σ<-comm f (suc m) (suc n)

module SemiringSummationProperties {c e} (SR : Semiring c e) where
  open Semiring SR
  open MonoidSummation +-monoid
  open CommutativeMonoidSummationProperties +-commutativeMonoid public
  open SetoidReasoning setoid

  Σ<-*-commute : ∀ f n c → Σ< (λ k → c * f k) n ≈ c * Σ< f n
  Σ<-*-commute f ℕ.zero c  = sym $ zeroʳ c
  Σ<-*-commute f (suc n) c = begin
    c * f n + Σ< (λ k → c * f k) n ≈⟨ +-congˡ $ Σ<-*-commute f n c ⟩
    c * f n + c * Σ< f n           ≈⟨ sym $ distribˡ c (f n) (Σ< f n) ⟩
    c * (f n + Σ< f n)             ∎

  Σ≤-*-commute : ∀ f n c → Σ≤ (λ k → c * f k) n ≈ c * Σ≤ f n
  Σ≤-*-commute f n c = Σ<-*-commute f (suc n) c
