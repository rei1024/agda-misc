{-# OPTIONS --without-K --safe #-}

module Math.NumberTheory.Summation.Generic.Properties where

-- agda-stdlib
open import Algebra
import Algebra.Operations.CommutativeMonoid as CommutativeMonoidOperations
open import Data.Nat as ℕ hiding (_+_; _*_)
import Data.Fin as Fin
import Data.Nat.Properties as ℕₚ
open import Relation.Binary.PropositionalEquality as ≡ using (_≡_)
import Relation.Binary.Reasoning.Setoid as SetoidReasoning
open import Function.Core

-- agda-misc
open import Math.NumberTheory.Summation.Generic
import Math.NumberTheory.Summation.Generic.Properties.Lemma as Lemma

module MonoidSummationProperties {c e} (M : Monoid c e) where
  open MonoidSummation M
  open Monoid M
  open SetoidReasoning setoid

  Σ<-cong : ∀ {f g m n} → (∀ x → f x ≈ g x) → m ≡ n → Σ< f m ≈ Σ< g n
  Σ<-cong {f} {g} {0}     {.0}       f≈g ≡.refl = refl
  Σ<-cong {f} {g} {suc m} {.(suc m)} f≈g ≡.refl = begin
    Σ< f m ∙ f m ≈⟨ ∙-cong (Σ<-cong {m = m} {n = m} f≈g ≡.refl) (f≈g m) ⟩
    Σ< g m ∙ g m ∎

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

  Σ<range-cong₁ : ∀ {f g : ℕ → Carrier} m n →
    (∀ x → f x ≈ g x) → Σ<range f m n ≈ Σ<range g m n
  Σ<range-cong₁ m n f≈g = Σ<range-cong {m = m} {o = n} f≈g ≡.refl ≡.refl

  Σ<range-cong₂₃ : ∀ (f : ℕ → Carrier) {m n o p} →
    m ≡ n → o ≡ p → Σ<range f m o ≈ Σ<range f n p
  Σ<range-cong₂₃ f ≡.refl ≡.refl = refl

  Σ<range-cong₂ : ∀ (f : ℕ → Carrier) {m n} o →
    m ≡ n → Σ<range f m o ≈ Σ<range f n o
  Σ<range-cong₂ f o m≡n = Σ<range-cong₂₃ f {o = o} m≡n ≡.refl

  Σ<range-cong₃ : ∀ (f : ℕ → Carrier) m {n o} →
    n ≡ o → Σ<range f m n ≈ Σ<range f m o
  Σ<range-cong₃ f m n≡o = Σ<range-cong₂₃ f {m = m} ≡.refl n≡o

  Σ≤range-cong : ∀ {f g : ℕ → Carrier} {m n o p} →
    (∀ x → f x ≈ g x) → m ≡ n → o ≡ p → Σ≤range f m o ≈ Σ≤range g n p
  Σ≤range-cong f≈g m≡n o≡p = Σ<range-cong f≈g m≡n (≡.cong suc o≡p)

  Σ<-0 : ∀ n → Σ< (λ _ → ε) n ≈ ε
  Σ<-0 zero    = refl
  Σ<-0 (suc n) = begin
    Σ< (λ _ → ε) n ∙ ε ≈⟨ ∙-congʳ $ Σ<-0 n ⟩
    ε ∙ ε              ≈⟨ identityʳ ε ⟩
    ε                  ∎

  Σ≤-0 : ∀ n → Σ≤ (λ _ → ε) n ≈ ε
  Σ≤-0 n = Σ<-0 (suc n)

  Σ<[f,1]≈f[0] : ∀ f → Σ< f 1 ≈ f 0
  Σ<[f,1]≈f[0] f = identityˡ (f 0)

  Σ≤[f,0]≈f[0] : ∀ f → Σ≤ f 0 ≈ f 0
  Σ≤[f,0]≈f[0] f = Σ<[f,1]≈f[0] f

  n≤m⇒Σ<range[f,m,n]≈0 : ∀ f {m n} → n ≤ m → Σ<range f m n ≈ ε
  n≤m⇒Σ<range[f,m,n]≈0 f {m} {n} n≤m = begin
    Σ< (λ k → f (m ℕ.+ k)) (n ∸ m) ≈⟨ Σ<-congˡ (λ k → f (m ℕ.+ k)) $ ℕₚ.m≤n⇒m∸n≡0 n≤m ⟩
    Σ< (λ k → f (m ℕ.+ k)) 0       ∎

  Σ<range[f,n,n]≈0 : ∀ f n → Σ<range f n n ≈ ε
  Σ<range[f,n,n]≈0 f n = n≤m⇒Σ<range[f,m,n]≈0 f {n} {n} ℕₚ.≤-refl

  n<m⇒Σ≤range[f,m,n]≈0 : ∀ f {m n} → n < m → Σ≤range f m n ≈ ε
  n<m⇒Σ≤range[f,m,n]≈0 f {m} {n} n<m = n≤m⇒Σ<range[f,m,n]≈0 f n<m

  Σ≤range[f,n,n]≈f[n] : ∀ f n → Σ≤range f n n ≈ f n
  Σ≤range[f,n,n]≈f[n] f n = begin
    Σ< (λ k → f (n ℕ.+ k)) (suc n ∸ n)
      ≈⟨ Σ<-congˡ (λ k → f (n ℕ.+ k)) $ ℕₚ.m+n∸n≡m 1 n ⟩
    Σ< (λ k → f (n ℕ.+ k)) 1
      ≈⟨ Σ<[f,1]≈f[0] (λ k → f (n ℕ.+ k)) ⟩
    f (n ℕ.+ 0)
      ≈⟨ reflexive (≡.cong f (ℕₚ.+-identityʳ n)) ⟩
    f n
      ∎

  Σ<-+ : ∀ f m n → Σ< f (m ℕ.+ n) ≈ Σ< f m ∙ Σ< (λ k → f (m ℕ.+ k)) n
  Σ<-+ f m zero    = begin
    Σ< f (m ℕ.+ 0) ≈⟨ Σ<-congˡ f $ ℕₚ.+-identityʳ m ⟩
    Σ< f m         ≈⟨ sym $ identityʳ (Σ< f m) ⟩
    Σ< f m ∙ ε     ∎
  Σ<-+ f m (suc n) = begin
    Σ< f (m ℕ.+ suc n)
      ≈⟨ Σ<-congˡ f $ ℕₚ.+-suc m n ⟩
    Σ< f (suc m ℕ.+ n)
      ≡⟨⟩
    Σ< f (m ℕ.+ n) ∙ f (m ℕ.+ n)
      ≈⟨ ∙-congʳ $ Σ<-+ f m n ⟩
    Σ< f m ∙ Σ< (λ k → f (m ℕ.+ k)) n ∙ f (m ℕ.+ n)
      ≈⟨ assoc (Σ< f m) (Σ< (λ k → f (m ℕ.+ k)) n) (f (m ℕ.+ n)) ⟩
    Σ< f m ∙ Σ< (λ k → f (m ℕ.+ k)) (suc n)
      ∎

  Σ≤-Σ<-+ : ∀ f m n →
    Σ≤ f (m ℕ.+ n) ≈ Σ≤ f m ∙ Σ< (λ k → f (1 ℕ.+ m ℕ.+ k)) n
  Σ≤-Σ<-+ f m n = Σ<-+ f (suc m) n

  Σ≤-+ : ∀ f m n →
    Σ≤ f (1 ℕ.+ m ℕ.+ n) ≈ Σ≤ f m ∙ Σ≤ (λ k → f (1 ℕ.+ m ℕ.+ k)) n
  Σ≤-+ f m n = begin
    Σ< f (2 ℕ.+ m ℕ.+ n)
      ≈⟨ Σ<-congˡ f $ Lemma.lemma₁ m n ⟩
    Σ< f (suc m ℕ.+ suc n)
      ≈⟨ Σ<-+ f (suc m) (suc n) ⟩
    Σ< f (suc m) ∙ Σ< (λ k → f (1 ℕ.+ m ℕ.+ k)) (suc n)
      ∎

  Σ<-push-suc : ∀ f n → Σ< f (suc n) ≈ f 0 ∙ Σ< (λ k → f (suc k)) n
  Σ<-push-suc f n = begin
    Σ< f (suc n)                    ≈⟨ Σ<-+ f 1 n ⟩
    Σ< f 1 ∙ Σ< (λ k → f (suc k)) n ≈⟨ ∙-congʳ $ Σ<[f,1]≈f[0] f ⟩
    f 0 ∙ Σ< (λ k → f (suc k)) n    ∎

  Σ≤-push-suc : ∀ f n → Σ≤ f (suc n) ≈ f 0 ∙ Σ≤ (λ k → f (suc k)) n
  Σ≤-push-suc f n = Σ<-push-suc f (suc n)

  Σ<range[f,0,n]≈Σ<[f,n] : ∀ f n → Σ<range f 0 n ≈ Σ< f n
  Σ<range[f,0,n]≈Σ<[f,n] f n = refl

  Σ≤range[f,0,n]≈Σ≤[f,n] : ∀ f n → Σ≤range f 0 n ≈ Σ≤ f n
  Σ≤range[f,0,n]≈Σ≤[f,n] f n = refl

  Σ<range[f,m,m+n+o]≈Σ<range[f,m,m+n]+Σ<range[m+n,m+n+o] : ∀ f m n o →
    Σ<range f m (m ℕ.+ n ℕ.+ o) ≈
    Σ<range f m (m ℕ.+ n) ∙ Σ<range f (m ℕ.+ n) (m ℕ.+ n ℕ.+ o)
  Σ<range[f,m,m+n+o]≈Σ<range[f,m,m+n]+Σ<range[m+n,m+n+o] f m n o = begin
    Σ< f′ (m+n+o ∸ m)
      ≈⟨ Σ<-congˡ f′ (≡.cong (_∸ m) $ ℕₚ.+-assoc m n o) ⟩
    Σ< f′ (m ℕ.+ n+o ∸ m)
      ≈⟨ Σ<-congˡ f′ (ℕₚ.m+n∸m≡n m n+o) ⟩
    Σ< f′ n+o
      ≈⟨ Σ<-+ f′ n o ⟩
    Σ< f′ n ∙ Σ< (λ k → f (m ℕ.+ (n ℕ.+ k))) o
      ≈⟨ ∙-cong (sym $ Σ<-congˡ f′ $ ℕₚ.m+n∸m≡n m n)
                (sym $ Σ<-cong (λ x → reflexive (≡.cong f (ℕₚ.+-assoc m n x)))
                               (ℕₚ.m+n∸m≡n m+n o)) ⟩
    Σ< f′ (m+n ∸ m) ∙ Σ< (λ k → f (m+n ℕ.+ k)) (m+n+o ∸ m+n)
      ∎
    where
    m+n = m ℕ.+ n
    n+o = n ℕ.+ o
    m+n+o = m+n ℕ.+ o
    f′ = λ k → f (m ℕ.+ k)

  Σ<range[f,m,n]≈Σ<range[f,m,o]+Σ<range[f,o,n] : ∀ f {m n o} →
    m ≤ o → o ≤ n →
    Σ<range f m n ≈ Σ<range f m o ∙ Σ<range f o n
  Σ<range[f,m,n]≈Σ<range[f,m,o]+Σ<range[f,o,n] f {m} {n} {o} m≤o o≤n = begin
    Σ<range f m n
      ≈⟨ reflexive (≡.cong (Σ<range f m) n≡m+p+q) ⟩
    Σ<range f m m+p+q
      ≈⟨ Σ<range[f,m,m+n+o]≈Σ<range[f,m,m+n]+Σ<range[m+n,m+n+o] f m p q ⟩
    Σ<range f m m+p ∙ Σ<range f m+p m+p+q
      ≈⟨ sym $ ∙-cong (Σ<range-cong₃ f m o≡m+p) (Σ<range-cong₂₃ f o≡m+p n≡m+p+q) ⟩
    Σ<range f m o ∙ Σ<range f o n
      ∎
    where
    p = o ∸ m
    q = n ∸ o
    m+p = m ℕ.+ p
    m+p+q = m+p ℕ.+ q
    o≡m+p : o ≡ m+p
    o≡m+p = ≡.sym $ ℕₚ.m+[n∸m]≡n m≤o
    n≡m+p+q : n ≡ m+p+q
    n≡m+p+q = ≡.sym ( ≡R.begin
      m ℕ.+ p ℕ.+ q ≡R.≡⟨ ≡.cong (ℕ._+ q) $ ≡.sym o≡m+p ⟩
      o ℕ.+ (n ∸ o) ≡R.≡⟨ ℕₚ.m+[n∸m]≡n o≤n ⟩
      n             ≡R.∎ )
      where module ≡R = ≡.≡-Reasoning

module CommutativeMonoidSummationProperties
  {c e} (CM : CommutativeMonoid c e) where
  open CommutativeMonoid CM
  open MonoidSummation monoid
  open MonoidSummationProperties monoid public
  open CommutativeMonoidOperations CM
  open SetoidReasoning setoid

  private
    n×x+x≈x+n×x : ∀ n x → n × x ∙ x ≈ x ∙ n × x
    n×x+x≈x+n×x zero    x = trans (identityˡ x) (sym $ identityʳ x)
    n×x+x≈x+n×x (suc n) x = begin
      x ∙ n × x ∙ x   ≈⟨ assoc x (n × x) x ⟩
      x ∙ (n × x ∙ x) ≈⟨ ∙-congˡ $ n×x+x≈x+n×x n x ⟩
      x ∙ (x ∙ n × x) ∎

  Σ<-const : ∀ x n → Σ< (const x) n ≈ n × x
  Σ<-const x zero    = refl
  Σ<-const x (suc n) = begin
    Σ< (const x) n ∙ x ≈⟨ ∙-congʳ $ Σ<-const x n ⟩
    n × x ∙ x          ≈⟨ n×x+x≈x+n×x n x ⟩
    x ∙ n × x          ∎

  Σ≤-const : ∀ x n → Σ≤ (const x) n ≈ suc n × x
  Σ≤-const x n = Σ<-const x (suc n)

  Σ<range-const : ∀ x m n → Σ<range (const x) m n ≈ (n ∸ m) × x
  Σ<range-const x m n = Σ<-const x (n ∸ m)

  Σ≤range-const : ∀ x m n → Σ≤range (const x) m n ≈ (suc n ∸ m) × x
  Σ≤range-const x m n = Σ<range-const x m (suc n)

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
    Σ< (λ k → f k ∙ g k) n ∙ (f n ∙ g n) ≈⟨ ∙-congʳ $ Σ<-distrib-+ f g n ⟩
    (Σ< f n ∙ Σ< g n) ∙ (f n ∙ g n)      ≈⟨ lemma (Σ< f n) (Σ< g n) (f n) (g n) ⟩
    (Σ< f n ∙ f n) ∙ (Σ< g n ∙ g n)      ∎

  Σ≤-distrib-+ : ∀ f g n → Σ≤ (λ k → f k ∙ g k) n ≈ Σ≤ f n ∙ Σ≤ g n
  Σ≤-distrib-+ f g n = Σ<-distrib-+ f g (suc n)

  Σ<range-distrib-+ : ∀ f g m n →
    Σ<range (λ k → f k ∙ g k) m n ≈ Σ<range f m n ∙ Σ<range g m n
  Σ<range-distrib-+ f g m n =
    Σ<-distrib-+ (λ k → f (m ℕ.+ k)) (λ k → g (m ℕ.+ k)) (n ∸ m)

  Σ≤range-distrib-+ : ∀ f g m n →
    Σ≤range (λ k → f k ∙ g k) m n ≈ Σ≤range f m n ∙ Σ≤range g m n
  Σ≤range-distrib-+ f g m n = Σ<range-distrib-+ f g m (suc n)

  Σ<-comm : ∀ (f : ℕ → ℕ → Carrier) m n →
    Σ< (λ i → Σ< (λ j → f i j) n) m ≈ Σ< (λ j → Σ< (λ i → f i j) m) n
  Σ<-comm f zero    n = sym $ Σ<-0 n
  Σ<-comm f (suc m) n = begin
    Σ< (λ i → Σ< (f i) n) (suc m)
     ≡⟨⟩
    Σ< (λ i → Σ< (f i) n) m ∙ Σ< (f m) n
      ≈⟨ ∙-congʳ $ Σ<-comm f m n ⟩
    Σ< (λ j → Σ< (λ i → f i j) m) n ∙ Σ< (λ j → f m j) n
      ≈⟨ sym $ Σ<-distrib-+ (λ j → Σ< (λ i → f i j) m) (λ j → f m j) n ⟩
    Σ< (λ j → Σ< (λ i → f i j) m ∙ f m j) n
      ≡⟨⟩
    Σ< (λ j → Σ< (λ i → f i j) (suc m)) n
      ∎

  Σ≤-comm : ∀ (f : ℕ → ℕ → Carrier) m n →
    Σ≤ (λ i → Σ≤ (λ j → f i j) n) m ≈ Σ≤ (λ j → Σ≤ (λ i → f i j) m) n
  Σ≤-comm f m n = Σ<-comm f (suc m) (suc n)

  Σ<range-comm : ∀ (f : ℕ → ℕ → Carrier) m n o p →
    Σ<range (λ i → Σ<range (λ j → f i j) o p) m n ≈
    Σ<range (λ j → Σ<range (λ i → f i j) m n) o p
  Σ<range-comm f m n o p =
    Σ<-comm (λ i j → f (m ℕ.+ i) (o ℕ.+ j)) (n ∸ m) (p ∸ o)

  Σ≤range-comm : ∀ (f : ℕ → ℕ → Carrier) m n o p →
    Σ≤range (λ i → Σ≤range (λ j → f i j) o p) m n ≈
    Σ≤range (λ j → Σ≤range (λ i → f i j) m n) o p
  Σ≤range-comm f m n o p = Σ<range-comm f m (suc n) o (suc p)

  Σ<-sumₜ-syntax : ∀ f n → Σ< f n ≈ sumₜ-syntax n (λ i → f (Fin.toℕ i))
  Σ<-sumₜ-syntax f 0       = refl
  Σ<-sumₜ-syntax f (suc n) = begin
    Σ< f (suc n)
      ≈⟨ Σ<-push-suc f n ⟩
    f 0 ∙ Σ< (λ k → f (suc k)) n
      ≈⟨ ∙-congˡ $ Σ<-sumₜ-syntax (λ k → f (suc k)) n ⟩
    f 0 ∙ sumₜ-syntax n (λ i → f (Fin.toℕ (Fin.suc i)))
      ∎

module SemiringSummationProperties {c e} (SR : Semiring c e) where
  open Semiring SR
  open MonoidSummation +-monoid
  open CommutativeMonoidSummationProperties +-commutativeMonoid public
  open SetoidReasoning setoid

  Σ<-*-commute : ∀ f n c → Σ< (λ k → c * f k) n ≈ c * Σ< f n
  Σ<-*-commute f ℕ.zero c  = sym $ zeroʳ c
  Σ<-*-commute f (suc n) c = begin
    Σ< (λ k → c * f k) n + c * f n ≈⟨ +-congʳ $ Σ<-*-commute f n c ⟩
    c * Σ< f n + c * f n           ≈⟨ sym $ distribˡ c (Σ< f n) (f n) ⟩
    c * (Σ< f n + f n)             ∎

  Σ≤-*-commute : ∀ f n c → Σ≤ (λ k → c * f k) n ≈ c * Σ≤ f n
  Σ≤-*-commute f n c = Σ<-*-commute f (suc n) c

  Σ<range-*-commute : ∀ f m n c →
    Σ<range (λ k → c * f k) m n ≈ c * Σ<range f m n
  Σ<range-*-commute f m n c = Σ<-*-commute (λ k → f (m ℕ.+ k)) (n ∸ m) c

  Σ≤range-*-commute : ∀ f m n c →
    Σ≤range (λ k → c * f k) m n ≈ c * Σ≤range f m n
  Σ≤range-*-commute f m n c = Σ<range-*-commute f m (suc n) c

module GroupSummationProperties {c e} (G : Group c e) where
