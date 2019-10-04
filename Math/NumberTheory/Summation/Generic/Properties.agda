{-# OPTIONS --without-K --safe #-}

module Math.NumberTheory.Summation.Generic.Properties where

-- agda-stdlib
open import Algebra
import Algebra.Operations.CommutativeMonoid as CommutativeMonoidOperations
open import Data.Nat as ℕ hiding (_+_; _*_)
import Data.Fin as Fin
import Data.Nat.Properties as ℕₚ
open import Relation.Nullary
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

  Σ<-cong : ∀ {m n f g} → m ≡ n → (∀ x → f x ≈ g x) → Σ< m f ≈ Σ< n g
  Σ<-cong {0}     {.0}       {f} {g} ≡.refl f≈g = refl
  Σ<-cong {suc m} {.(suc m)} {f} {g} ≡.refl f≈g = begin
    Σ< m f ∙ f m ≈⟨ ∙-cong (Σ<-cong {m = m} {n = m} ≡.refl f≈g) (f≈g m) ⟩
    Σ< m g ∙ g m ∎

  Σ<-congˡ : ∀ n {f g} → (∀ x → f x ≈ g x) → Σ< n f ≈ Σ< n g
  Σ<-congˡ n f≈g = Σ<-cong {m = n} ≡.refl f≈g

  Σ<-congʳ : ∀ {m n} f → m ≡ n → Σ< m f ≈ Σ< n f
  Σ<-congʳ f m≡n = Σ<-cong {f = f} m≡n (λ _ → refl)

  Σ≤-cong : ∀ {m n f g} → m ≡ n → (∀ x → f x ≈ g x) → Σ≤ m f ≈ Σ≤ n g
  Σ≤-cong m≡n f≈g = Σ<-cong (≡.cong suc m≡n) f≈g

  Σ≤-congˡ : ∀ n {f g} → (∀ x → f x ≈ g x) → Σ≤ n f ≈ Σ≤ n g
  Σ≤-congˡ n = Σ<-congˡ (suc n)

  Σ≤-congʳ : ∀ {m n} f → m ≡ n → Σ≤ m f ≈ Σ≤ n f
  Σ≤-congʳ f m≡n = Σ<-congʳ f (≡.cong suc m≡n)

  Σ<range-cong : ∀ {m n o p} {f g : ℕ → Carrier} → m ≡ n → o ≡ p →
    (∀ x → f x ≈ g x) → Σ<range m o f ≈ Σ<range n p g
  Σ<range-cong {m} {.m} {o} {.o} {f} {g} ≡.refl ≡.refl f≈g = begin
    Σ< (o ∸ m) (λ k → f (m ℕ.+ k)) ≈⟨ Σ<-congˡ (o ∸ m) (λ x → f≈g (m ℕ.+ x)) ⟩
    Σ< (o ∸ m) (λ k → g (m ℕ.+ k)) ∎

  Σ<range-cong₃ : ∀ m n {f g : ℕ → Carrier} →
    (∀ x → f x ≈ g x) → Σ<range m n f ≈ Σ<range m n g
  Σ<range-cong₃ m n f≈g = Σ<range-cong {m = m} {o = n} ≡.refl ≡.refl f≈g

  Σ<range-cong₁₂ : ∀ {m n o p} (f : ℕ → Carrier) →
    m ≡ n → o ≡ p → Σ<range m o f ≈ Σ<range n p f
  Σ<range-cong₁₂ f ≡.refl ≡.refl = refl

  Σ<range-cong₁ : ∀ {m n} o (f : ℕ → Carrier)→
    m ≡ n → Σ<range m o f ≈ Σ<range n o f
  Σ<range-cong₁ o f m≡n = Σ<range-cong₁₂ {o = o} f m≡n ≡.refl

  Σ<range-cong₂ : ∀ m {n o} (f : ℕ → Carrier) →
    n ≡ o → Σ<range m n f ≈ Σ<range m o f
  Σ<range-cong₂ m f n≡o = Σ<range-cong₁₂ {m = m} f ≡.refl n≡o

  Σ≤range-cong : ∀ {m n o p} {f g : ℕ → Carrier} →
    m ≡ n → o ≡ p → (∀ x → f x ≈ g x) → Σ≤range m o f ≈ Σ≤range n p g
  Σ≤range-cong m≡n o≡p f≈g = Σ<range-cong m≡n (≡.cong suc o≡p) f≈g

  Σ<-congˡ-with-< : ∀ n {f g} → (∀ i → i < n → f i ≈ g i) → Σ< n f ≈ Σ< n g
  Σ<-congˡ-with-< 0       {f} {g} f≈g = refl
  Σ<-congˡ-with-< (suc n) {f} {g} f≈g =
    ∙-cong (Σ<-congˡ-with-< n (λ i i<n → f≈g i (ℕₚ.≤-step i<n))) (f≈g n ℕₚ.≤-refl)

  Σ≤-congˡ-with-≤ : ∀ n {f g} → (∀ i → i ≤ n → f i ≈ g i) → Σ≤ n f ≈ Σ≤ n g
  Σ≤-congˡ-with-≤ n f≈g = Σ<-congˡ-with-< (suc n) λ i 1+i≤1+n → f≈g i (ℕₚ.≤-pred 1+i≤1+n)

  Σ<-0 : ∀ n → Σ< n (λ _ → ε) ≈ ε
  Σ<-0 zero    = refl
  Σ<-0 (suc n) = begin
    Σ< n (λ _ → ε) ∙ ε ≈⟨ ∙-congʳ $ Σ<-0 n ⟩
    ε ∙ ε              ≈⟨ identityʳ ε ⟩
    ε                  ∎

  Σ≤-0 : ∀ n → Σ≤ n (λ _ → ε) ≈ ε
  Σ≤-0 n = Σ<-0 (suc n)

  Σ<[1,f]≈f[0] : ∀ f → Σ< 1 f ≈ f 0
  Σ<[1,f]≈f[0] f = identityˡ (f 0)

  Σ≤[0,f]≈f[0] : ∀ f → Σ≤ 0 f ≈ f 0
  Σ≤[0,f]≈f[0] f = Σ<[1,f]≈f[0] f

  n≤m⇒Σ<range[m,n,f]≈0 : ∀ {m n} f → n ≤ m → Σ<range m n f ≈ ε
  n≤m⇒Σ<range[m,n,f]≈0 {m} {n} f n≤m = begin
    Σ< (n ∸ m) (λ k → f (m ℕ.+ k)) ≈⟨ Σ<-congʳ (λ k → f (m ℕ.+ k)) $ ℕₚ.m≤n⇒m∸n≡0 n≤m ⟩
    Σ< 0       (λ k → f (m ℕ.+ k)) ∎

  Σ<range-cong₃-with-< : ∀ m n {f g} →
    (∀ i → m ≤ i → i < n → f i ≈ g i) → Σ<range m n f ≈ Σ<range m n g
  Σ<range-cong₃-with-< m n {f} {g} f≈g with m ℕₚ.≤? n
  ... | yes m≤n =
    Σ<-congˡ-with-< (n ∸ m) {λ i → f (m ℕ.+ i)} {λ i → g (m ℕ.+ i)}
      λ i i<n∸m → f≈g (m ℕ.+ i) (ℕₚ.m≤m+n m i) (≤R.begin
        1 ℕ.+ (m ℕ.+ i) ≤R.≡⟨ ≡.cong (1 ℕ.+_) $ ℕₚ.+-comm m i ⟩
        suc i ℕ.+ m     ≤R.≤⟨ ℕₚ.+-monoˡ-≤ m i<n∸m ⟩
        o ℕ.+ m         ≤R.≡⟨ ≡.sym n≡o+m ⟩
        n               ≤R.∎ )
      where o = n ∸ m
            n≡o+m : n ≡ o ℕ.+ m
            n≡o+m = ≡.sym $ ℕₚ.m∸n+n≡m m≤n
            module ≤R = ℕₚ.≤-Reasoning
  ... | no m≰n = trans (n≤m⇒Σ<range[m,n,f]≈0 f n≤m) (sym $ n≤m⇒Σ<range[m,n,f]≈0 g n≤m)
    where n≤m = ℕₚ.<⇒≤ $ ℕₚ.≰⇒> m≰n

  Σ≤range-cong₃-with-≤ : ∀ m n {f g} →
    (∀ i → m ≤ i → i ≤ n → f i ≈ g i) → Σ≤range m n f ≈ Σ≤range m n g
  Σ≤range-cong₃-with-≤ m n {f} {g} f≈g = Σ<range-cong₃-with-< m (suc n)
    λ i i≤n 1+i≤1+n → f≈g i i≤n (ℕₚ.≤-pred 1+i≤1+n)

  Σ<range[n,n,f]≈0 : ∀ n f → Σ<range n n f ≈ ε
  Σ<range[n,n,f]≈0 n f = n≤m⇒Σ<range[m,n,f]≈0 {n} {n} f ℕₚ.≤-refl

  n<m⇒Σ≤range[m,n,f]≈0 : ∀ {m n} f → n < m → Σ≤range m n f ≈ ε
  n<m⇒Σ≤range[m,n,f]≈0 {m} {n} f n<m = n≤m⇒Σ<range[m,n,f]≈0 f n<m

  Σ<range[n,1+n,f]≈f[n] : ∀ n f → Σ<range n (suc n) f ≈ f n
  Σ<range[n,1+n,f]≈f[n] n f = begin
    Σ< (suc n ∸ n) (λ k → f (n ℕ.+ k))
      ≈⟨ Σ<-congʳ (λ k → f (n ℕ.+ k)) $ ℕₚ.m+n∸n≡m 1 n ⟩
    Σ< 1 (λ k → f (n ℕ.+ k))
      ≈⟨ Σ<[1,f]≈f[0] (λ k → f (n ℕ.+ k)) ⟩
    f (n ℕ.+ 0)
      ≈⟨ reflexive (≡.cong f (ℕₚ.+-identityʳ n)) ⟩
    f n
      ∎

  Σ≤range[n,n,f]≈f[n] : ∀ n f → Σ≤range n n f ≈ f n
  Σ≤range[n,n,f]≈f[n] = Σ<range[n,1+n,f]≈f[n]

  Σ<-+ : ∀ m n f → Σ< (m ℕ.+ n) f ≈ Σ< m f ∙ Σ< n (λ k → f (m ℕ.+ k))
  Σ<-+ m zero    f = begin
    Σ< (m ℕ.+ 0) f ≈⟨ Σ<-congʳ f $ ℕₚ.+-identityʳ m ⟩
    Σ< m f         ≈⟨ sym $ identityʳ (Σ< m f) ⟩
    Σ< m f ∙ ε     ∎
  Σ<-+ m (suc n) f = begin
    Σ< (m ℕ.+ suc n) f
      ≈⟨ Σ<-congʳ f $ ℕₚ.+-suc m n ⟩
    Σ< (suc m ℕ.+ n) f
      ≡⟨⟩
    Σ< (m ℕ.+ n) f ∙ f (m ℕ.+ n)
      ≈⟨ ∙-congʳ $ Σ<-+ m n f ⟩
    Σ< m f ∙ Σ< n (λ k → f (m ℕ.+ k)) ∙ f (m ℕ.+ n)
      ≈⟨ assoc (Σ< m f) (Σ< n (λ k → f (m ℕ.+ k))) (f (m ℕ.+ n)) ⟩
    Σ< m f ∙ Σ< (suc n) (λ k → f (m ℕ.+ k))
      ∎

  Σ≤-Σ<-+ : ∀ m n f →
    Σ≤ (m ℕ.+ n) f ≈ Σ≤ m f ∙ Σ< n (λ k → f (1 ℕ.+ m ℕ.+ k))
  Σ≤-Σ<-+ m n f = Σ<-+ (suc m) n f

  Σ≤-+ : ∀ m n f →
    Σ≤ (1 ℕ.+ m ℕ.+ n) f ≈ Σ≤ m f ∙ Σ≤ n (λ k → f (1 ℕ.+ m ℕ.+ k))
  Σ≤-+ m n f = begin
    Σ< (2 ℕ.+ m ℕ.+ n) f
      ≈⟨ Σ<-congʳ f $ Lemma.lemma₁ m n ⟩
    Σ< (suc m ℕ.+ suc n) f
      ≈⟨ Σ<-+ (suc m) (suc n) f ⟩
    Σ< (suc m) f ∙ Σ< (suc n) (λ k → f (1 ℕ.+ m ℕ.+ k))
      ∎

  Σ<-push-suc : ∀ n f → Σ< (suc n) f ≈ f 0 ∙ Σ< n (λ k → f (suc k))
  Σ<-push-suc n f = begin
    Σ< (suc n) f                   ≈⟨ Σ<-+ 1 n f ⟩
    Σ< 1 f ∙ Σ< n (λ k → f (suc k)) ≈⟨ ∙-congʳ $ Σ<[1,f]≈f[0] f ⟩
    f 0 ∙ Σ< n (λ k → f (suc k))    ∎

  Σ≤-push-suc : ∀ n f → Σ≤ (suc n) f ≈ f 0 ∙ Σ≤ n (λ k → f (suc k))
  Σ≤-push-suc n f = Σ<-push-suc (suc n) f

  Σ<range[0,n,f]≈Σ<[n,f] : ∀ n f → Σ<range 0 n f ≈ Σ< n f
  Σ<range[0,n,f]≈Σ<[n,f] n f = refl

  Σ≤range[0,n,f]≈Σ≤[n,f] : ∀ n f → Σ≤range 0 n f ≈ Σ≤ n f
  Σ≤range[0,n,f]≈Σ≤[n,f] n f = refl

  Σ<range[m,m+n+o,f]≈Σ<range[m,m+n,f]+Σ<range[m+n,m+n+o,f] : ∀ m n o f →
    Σ<range m (m ℕ.+ n ℕ.+ o) f ≈
    Σ<range m (m ℕ.+ n) f ∙ Σ<range (m ℕ.+ n) (m ℕ.+ n ℕ.+ o) f
  Σ<range[m,m+n+o,f]≈Σ<range[m,m+n,f]+Σ<range[m+n,m+n+o,f] m n o f = begin
    Σ< (m+n+o ∸ m) f′
      ≈⟨ Σ<-congʳ f′ (≡.cong (_∸ m) $ ℕₚ.+-assoc m n o) ⟩
    Σ< (m ℕ.+ n+o ∸ m) f′
      ≈⟨ Σ<-congʳ f′ (ℕₚ.m+n∸m≡n m n+o) ⟩
    Σ< n+o f′
      ≈⟨ Σ<-+ n o f′ ⟩
    Σ< n f′ ∙ Σ< o (λ k → f (m ℕ.+ (n ℕ.+ k)))
      ≈⟨ ∙-cong (sym $ Σ<-congʳ f′ $ ℕₚ.m+n∸m≡n m n)
                (sym $ Σ<-cong (ℕₚ.m+n∸m≡n m+n o)
                               (λ x → reflexive (≡.cong f (ℕₚ.+-assoc m n x)))) ⟩
    Σ< (m+n ∸ m) f′ ∙ Σ< (m+n+o ∸ m+n) (λ k → f (m+n ℕ.+ k))
      ∎
    where
    m+n = m ℕ.+ n
    n+o = n ℕ.+ o
    m+n+o = m+n ℕ.+ o
    f′ = λ k → f (m ℕ.+ k)

  Σ<range[m,n,f]≈Σ<range[m,o,f]+Σ<range[o,n,f] : ∀ {m n o} f →
    m ≤ o → o ≤ n →
    Σ<range m n f ≈ Σ<range m o f ∙ Σ<range o n f
  Σ<range[m,n,f]≈Σ<range[m,o,f]+Σ<range[o,n,f] {m} {n} {o} f m≤o o≤n = begin
    Σ<range m n f
      ≈⟨ reflexive (≡.cong (λ v → Σ<range m v f) n≡m+p+q) ⟩
    Σ<range m m+p+q f
      ≈⟨ Σ<range[m,m+n+o,f]≈Σ<range[m,m+n,f]+Σ<range[m+n,m+n+o,f] m p q f ⟩
    Σ<range m m+p f ∙ Σ<range m+p m+p+q f
      ≈⟨ sym $ ∙-cong (Σ<range-cong₂ m f o≡m+p) (Σ<range-cong₁₂ f o≡m+p n≡m+p+q) ⟩
    Σ<range m o f ∙ Σ<range o n f
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

  -- Reindex
  Σ<range[m,n,f]≈Σ<range[o+m,o+n,i→f[i∸o]] : ∀ m n o f →
    Σ<range m n f ≈ Σ<range (o ℕ.+ m) (o ℕ.+ n) (λ i → f (i ∸ o))
  Σ<range[m,n,f]≈Σ<range[o+m,o+n,i→f[i∸o]] m n o f = begin
    Σ< (n ∸ m) (λ k → f (m ℕ.+ k))
      ≈⟨ Σ<-cong (≡.sym $ ℕₚ.[m+n]∸[m+o]≡n∸o o n m)
                 (λ x → reflexive $ ≡.cong f $ ≡.sym $ (≡R.begin
          o ℕ.+ m ℕ.+ x ∸ o   ≡R.≡⟨ ≡.cong (_∸ o) $ ℕₚ.+-assoc o m x ⟩
          o ℕ.+ (m ℕ.+ x) ∸ o ≡R.≡⟨ ℕₚ.m+n∸m≡n o (m ℕ.+ x) ⟩
          m ℕ.+ x             ≡R.∎ ))  ⟩
    Σ< ((o ℕ.+ n) ∸ (o ℕ.+ m)) (λ k → f ((o ℕ.+ m ℕ.+ k) ∸ o))
      ∎
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

  Σ<-const : ∀ n x → Σ< n (const x) ≈ n × x
  Σ<-const zero    x = refl
  Σ<-const (suc n) x = begin
    Σ< n (const x) ∙ x ≈⟨ ∙-congʳ $ Σ<-const n x ⟩
    n × x ∙ x          ≈⟨ n×x+x≈x+n×x n x ⟩
    x ∙ n × x          ∎

  Σ≤-const : ∀ n x → Σ≤ n (const x) ≈ suc n × x
  Σ≤-const n x = Σ<-const (suc n) x

  Σ<range-const : ∀ m n x → Σ<range m n (const x) ≈ (n ∸ m) × x
  Σ<range-const m n x = Σ<-const (n ∸ m) x

  Σ≤range-const : ∀ m n x → Σ≤range m n (const x) ≈ (suc n ∸ m) × x
  Σ≤range-const m n x = Σ<range-const m (suc n) x

  private
    lemma : ∀ a b c d → a ∙ b ∙ (c ∙ d) ≈ a ∙ c ∙ (b ∙ d)
    lemma a b c d = begin
      (a ∙ b) ∙ (c ∙ d) ≈⟨ assoc a b (c ∙ d) ⟩
      a ∙ (b ∙ (c ∙ d)) ≈⟨ sym $ ∙-congˡ $ assoc b c d ⟩
      a ∙ ((b ∙ c) ∙ d) ≈⟨ ∙-congˡ $ ∙-congʳ $ comm b c ⟩
      a ∙ ((c ∙ b) ∙ d) ≈⟨ ∙-congˡ $ assoc c b d ⟩
      a ∙ (c ∙ (b ∙ d)) ≈⟨ sym $ assoc a c (b ∙ d) ⟩
      (a ∙ c) ∙ (b ∙ d) ∎

  Σ<-distrib-+ : ∀ n f g → Σ< n (λ k → f k ∙ g k) ≈ Σ< n f ∙ Σ< n g
  Σ<-distrib-+ zero    f g = sym $ identityʳ ε
  Σ<-distrib-+ (suc n) f g = begin
    Σ< n (λ k → f k ∙ g k) ∙ (f n ∙ g n) ≈⟨ ∙-congʳ $ Σ<-distrib-+ n f g ⟩
    (Σ< n f ∙ Σ< n g) ∙ (f n ∙ g n)      ≈⟨ lemma (Σ< n f) (Σ< n g) (f n) (g n) ⟩
    (Σ< n f ∙ f n) ∙ (Σ< n g ∙ g n)      ∎

  Σ≤-distrib-+ : ∀ n f g → Σ≤ n (λ k → f k ∙ g k) ≈ Σ≤ n f ∙ Σ≤ n g
  Σ≤-distrib-+ n f g = Σ<-distrib-+ (suc n) f g

  Σ<range-distrib-+ : ∀ m n f g →
    Σ<range m n (λ k → f k ∙ g k) ≈ Σ<range m n f ∙ Σ<range m n g
  Σ<range-distrib-+ m n f g =
    Σ<-distrib-+ (n ∸ m) (λ k → f (m ℕ.+ k)) (λ k → g (m ℕ.+ k))

  Σ≤range-distrib-+ : ∀ m n f g →
    Σ≤range m n (λ k → f k ∙ g k) ≈ Σ≤range m n f ∙ Σ≤range m n g
  Σ≤range-distrib-+ m n f g = Σ<range-distrib-+ m (suc n) f g

  Σ<-comm : ∀ m n (f : ℕ → ℕ → Carrier) →
    Σ< m (λ i → Σ< n (λ j → f i j)) ≈ Σ< n (λ j → Σ< m (λ i → f i j))
  Σ<-comm zero    n f = sym $ Σ<-0 n
  Σ<-comm (suc m) n f = begin
    Σ< (suc m) (λ i → Σ< n (f i))
     ≡⟨⟩
    Σ< m (λ i → Σ< n (f i)) ∙ Σ< n (f m)
      ≈⟨ ∙-congʳ $ Σ<-comm m n f ⟩
    Σ< n (λ j → Σ< m (λ i → f i j)) ∙ Σ< n (λ j → f m j)
      ≈⟨ sym $ Σ<-distrib-+ n (λ j → Σ< m (λ i → f i j)) (λ j → f m j) ⟩
    Σ< n (λ j → Σ< m (λ i → f i j) ∙ f m j)
      ≡⟨⟩
    Σ< n (λ j → Σ< (suc m) (λ i → f i j))
      ∎

  Σ≤-comm : ∀ m n (f : ℕ → ℕ → Carrier) →
    Σ≤ m (λ i → Σ≤ n (λ j → f i j)) ≈ Σ≤ n (λ j → Σ≤ m (λ i → f i j))
  Σ≤-comm m n f = Σ<-comm (suc m) (suc n) f

  Σ<range-comm : ∀ m n o p (f : ℕ → ℕ → Carrier) →
    Σ<range m n (λ i → Σ<range o p (λ j → f i j)) ≈
    Σ<range o p (λ j → Σ<range m n (λ i → f i j))
  Σ<range-comm m n o p f =
    Σ<-comm (n ∸ m) (p ∸ o) (λ i j → f (m ℕ.+ i) (o ℕ.+ j))

  Σ≤range-comm : ∀ m n o p (f : ℕ → ℕ → Carrier) →
    Σ≤range m n (λ i → Σ≤range o p (λ j → f i j)) ≈
    Σ≤range o p (λ j → Σ≤range m n (λ i → f i j))
  Σ≤range-comm m n o p f = Σ<range-comm m (suc n) o (suc p) f

  Σ<-sumₜ-syntax : ∀ n f → Σ< n f ≈ sumₜ-syntax n (λ i → f (Fin.toℕ i))
  Σ<-sumₜ-syntax 0       f = refl
  Σ<-sumₜ-syntax (suc n) f = begin
    Σ< (suc n) f
      ≈⟨ Σ<-push-suc n f ⟩
    f 0 ∙ Σ< n (λ k → f (suc k))
      ≈⟨ ∙-congˡ $ Σ<-sumₜ-syntax n (λ k → f (suc k)) ⟩
    f 0 ∙ sumₜ-syntax n (λ i → f (Fin.toℕ (Fin.suc i)))
      ∎

  Σ<-reverse : ∀ n f → Σ< n f ≈ Σ< n (λ i → f (n ∸ suc i))
  Σ<-reverse 0       f = refl
  Σ<-reverse (suc n) f = begin
    Σ< (suc n) f
      ≈⟨ Σ<-push-suc n f ⟩
    f 0 ∙ Σ< n (λ i → f (suc i))
      ≈⟨ comm (f 0) (Σ< n (λ i → f (suc i))) ⟩
    Σ< n (λ i → f (suc i)) ∙ f 0
      ≈⟨ ∙-congʳ $ Σ<-reverse n (λ i → f (suc i)) ⟩
    Σ< n (λ i → f (suc (n ∸ suc i))) ∙ f 0
      ≈⟨ ∙-congʳ $ Σ<-congˡ-with-< n $ (λ i i<n → reflexive $ ≡.cong f $ ≡.sym $ ℕₚ.+-∸-assoc 1 i<n) ⟩
    Σ< n (λ i → f (suc n ∸ suc i)) ∙ f 0
      ≈⟨ ∙-congˡ $ reflexive $ ≡.cong f $ ≡.sym $ ℕₚ.n∸n≡0 (suc n) ⟩
    Σ< n (λ i → f (suc n ∸ suc i)) ∙ f (suc n ∸ suc n)
      ≡⟨⟩
    Σ< (suc n) (λ i → f (suc n ∸ suc i))
      ∎

  Σ≤-reverse : ∀ n f → Σ≤ n f ≈ Σ≤ n (λ i → f (n ∸ i))
  Σ≤-reverse n f = Σ<-reverse (suc n) f

module SemiringSummationProperties {c e} (SR : Semiring c e) where
  open Semiring SR
  open MonoidSummation +-monoid
  open CommutativeMonoidSummationProperties +-commutativeMonoid public
  open SetoidReasoning setoid

  Σ<-*-commute : ∀ n c f → Σ< n (λ k → c * f k) ≈ c * Σ< n f
  Σ<-*-commute ℕ.zero  c f = sym $ zeroʳ c
  Σ<-*-commute (suc n) c f = begin
    Σ< n (λ k → c * f k) + c * f n ≈⟨ +-congʳ $ Σ<-*-commute n c f ⟩
    c * Σ< n f + c * f n           ≈⟨ sym $ distribˡ c (Σ< n f) (f n) ⟩
    c * (Σ< n f + f n)             ∎

  Σ≤-*-commute : ∀ n c f → Σ≤ n (λ k → c * f k) ≈ c * Σ≤ n f
  Σ≤-*-commute n c f = Σ<-*-commute (suc n) c f

  Σ<range-*-commute : ∀ m n c f →
    Σ<range  m n (λ k → c * f k) ≈ c * Σ<range m n f
  Σ<range-*-commute m n c f = Σ<-*-commute (n ∸ m) c (λ k → f (m ℕ.+ k))

  Σ≤range-*-commute : ∀ m n c f →
    Σ≤range m n (λ k → c * f k) ≈ c * Σ≤range m n f
  Σ≤range-*-commute m n c f = Σ<range-*-commute m (suc n) c f

  Σ<-distrib-* : ∀ m n f g →
    Σ< m f * Σ< n g ≈ Σ< m (λ i → Σ< n (λ j → f i * g j))
  Σ<-distrib-* 0       n f g = zeroˡ (Σ< n g)
  Σ<-distrib-* (suc m) n f g = begin
    Σ< (suc m) f * Σ< n g
      ≡⟨⟩
    (Σ< m f + f m) * Σ< n g
      ≈⟨ distribʳ (Σ< n g) (Σ< m f) (f m) ⟩
    Σ< m f * Σ< n g + f m * Σ< n g
      ≈⟨ +-cong (Σ<-distrib-* m n f g) (sym $ Σ<-*-commute n (f m) g) ⟩
    Σ< m (λ i → Σ< n (λ j → f i * g j)) + Σ< n (λ j → f m * g j)
      ≡⟨⟩
    Σ< (suc m) (λ i → Σ< n (λ j → f i * g j))
      ∎

  Σ≤-distrib-* : ∀ m n f g →
    Σ≤ m f * Σ≤ n g ≈ Σ≤ m (λ i → Σ≤ n (λ j → f i * g j))
  Σ≤-distrib-* m n f g = Σ<-distrib-* (suc m) (suc n) f g

  Σ<range-distrib-* : ∀ m n o p f g →
    Σ<range m n f * Σ<range o p g ≈ Σ<range m n (λ i → Σ<range o p (λ j → f i * g j))
  Σ<range-distrib-* m n o p f g =
    Σ<-distrib-* (n ∸ m) (p ∸ o) (λ i → f (m ℕ.+ i)) λ j → g (o ℕ.+ j)

  Σ≤range-distrib-* : ∀ m n o p f g →
    Σ≤range m n f * Σ≤range o p g ≈ Σ≤range m n (λ i → Σ≤range o p (λ j → f i * g j))
  Σ≤range-distrib-* m n o p = Σ<range-distrib-* m (suc n) o (suc p)

module GroupSummationProperties {c e} (G : Group c e) where
  open Group G
  open MonoidSummation monoid
  open MonoidSummationProperties monoid
  open SetoidReasoning setoid

  Σ<-telescope : ∀ n (f : ℕ → Carrier) →
    Σ< n (λ i → f i - f (suc i)) ≈ f 0 - f n
  Σ<-telescope 0       f = sym $ inverseʳ (f 0)
  Σ<-telescope (suc n) f = begin
    Σ< n (λ i → f i - f (suc i)) ∙ (f n - f (suc n))
      ≈⟨ ∙-congʳ $ Σ<-telescope n f ⟩
    (f 0 - f n) ∙ (f n - f (suc n))
      ≈⟨ assoc (f 0) (f n ⁻¹) (f n - f (suc n)) ⟩
    f 0 ∙ (f n ⁻¹ ∙ (f n - f (suc n)))
      ≈⟨ ∙-congˡ $ sym $ assoc (f n ⁻¹) (f n) (f (suc n) ⁻¹) ⟩
    f 0 ∙ ((f n ⁻¹ ∙ f n) - f (suc n))
      ≈⟨ ∙-congˡ $ ∙-congʳ $ inverseˡ (f n) ⟩
    f 0 ∙ (ε - f (suc n))
      ≈⟨ ∙-congˡ $ identityˡ (f (suc n) ⁻¹) ⟩
    f 0 - f (suc n)
      ∎
