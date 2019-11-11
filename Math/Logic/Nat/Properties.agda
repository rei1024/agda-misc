-- Properties of natural number

{-# OPTIONS --without-K --safe #-}

-- agad-stdlib
open import Relation.Binary.PropositionalEquality

module Math.Logic.Nat.Properties
  {a}
  (N : Set a)
  (zero : N)
  (suc : N → N)
  (ind : ∀ {p} (P : N → Set p) → P zero → (∀ k → P k → P (suc k)) → ∀ n → P n)
  (ind-base : ∀ {p} (P : N → Set p) P-base P-step →
              ind P P-base P-step zero ≡ P-base)
  (ind-step : ∀ {p} (P : N → Set p) P-base P-step n →
              ind P P-base P-step (suc n) ≡ P-step n (ind P P-base P-step n))
  where

-- agda-stdlib
open import Axiom.UniquenessOfIdentityProofs
open import Level renaming (zero to lzero; suc to lsuc)
open import Data.Empty
open import Data.Unit using (⊤ ; tt)
open import Data.Product
import Data.Product.Properties as Prodₚ
open import Data.Sum as Sum
open import Data.Bool using (Bool; true; false)
open import Function.Base
import Relation.Binary as B
open import Relation.Nullary
import Relation.Nullary.Decidable as NDec

-- agda-misc
open import Math.Logic.Nat.Operations N zero suc ind ind-base ind-step

open ≡-Reasoning

private
  variable
    A : Set a

-- Properties of rec
rec-base : ∀ {A : Set a} (z : A) s → rec z s zero ≡ z
rec-base {A} z s = ind-base (λ _ → A) z λ k x → s x

rec-step : ∀ {A : Set a} (z : A) s n → rec z s (suc n) ≡ s (rec z s n)
rec-step {A} z s n = ind-step (λ _ → A) z (λ k x → s x) n

ind2-zz : ∀ {p} (P : N → N → Set p) Pzz Pmn→Pms Pmn→Psn →
  ind2 P Pzz Pmn→Pms Pmn→Psn zero zero ≡ Pzz
ind2-zz P Pzz Pmn→Pms Pmn→Psn = begin
  ind2 P Pzz Pmn→Pms Pmn→Psn zero zero
    ≡⟨⟩
  ind
      (λ o → P o zero)
      (ind (λ p → P zero p) Pzz (λ k Pzk → Pmn→Pms zero k Pzk) zero)
      (λ k Pkn → ind (λ r → P (suc k) r) (( λ k → ind (λ x → P x zero) Pzz (λ k₂ Pk₂zero → Pmn→Psn k₂ zero Pk₂zero) k) (suc k))
        (λ k₁ P[1+k,k₁] → Pmn→Pms (suc k) k₁ P[1+k,k₁]) zero)
      zero
    ≡⟨ ind-base _ _ _ ⟩
  ind (λ p → P zero p) Pzz (Pmn→Pms zero) zero
    ≡⟨ ind-base _ _ _ ⟩
  Pzz
    ∎
  where open ≡-Reasoning


---------------------------------------------------------------------------
-- Properties of pred

pred-zero : pred zero ≡ zero
pred-zero = ind-base (λ _ → N) zero (λ k x → k)

pred-suc : ∀ n → pred (suc n) ≡ n
pred-suc n = ind-step (λ _ → N) zero (λ k x → k) n

-- Properties of suc
suc-injective : ∀ {m n} → suc m ≡ suc n → m ≡ n
suc-injective {m} {n} 1+m≡1+n = begin
  m            ≡⟨ sym $ pred-suc m ⟩
  pred (suc m) ≡⟨ cong pred 1+m≡1+n ⟩
  pred (suc n) ≡⟨ pred-suc n ⟩
  n            ∎

-- Properties of caseNat
caseNat-base : ∀ {l} {A : Set l} (z s : A) → caseNat z s zero ≡ z
caseNat-base z s = ind-base (λ x → _) z λ k x → s

caseNat-step : ∀ {l} {A : Set l} (z s : A) n → caseNat z s (suc n) ≡ s
caseNat-step z s n = ind-step (λ x → _) z (λ k x → s) n

NotZero : ∀ n → Set
NotZero n = caseNat ⊥ ⊤ n

NotZero[zero]≡⊥ : NotZero zero ≡ ⊥
NotZero[zero]≡⊥ = caseNat-base ⊥ ⊤

NotZero[suc[n]]≡⊤ : ∀ n → NotZero (suc n) ≡ ⊤
NotZero[suc[n]]≡⊤ n = caseNat-step ⊥ ⊤ n

private
  transport : ∀ {a} {A B : Set a} → A ≡ B → A → B
  transport eq = subst id eq

NotZero[suc[n]] : ∀ (n : N) → NotZero (suc n)
NotZero[suc[n]] n = transport (sym $ NotZero[suc[n]]≡⊤ n) tt

s≢z : ∀ (n : N) → suc n ≢ zero
s≢z n eq = transport NotZero[zero]≡⊥ $ subst NotZero eq (NotZero[suc[n]] n)

z≢s : ∀ (n : N) → zero ≢ suc n
z≢s n eq = s≢z n (sym eq)

1+n≢n : ∀ n → suc n ≢ n
1+n≢n n = ind (λ x → suc x ≢ x) (s≢z zero)
  (λ k 1+k≢k 1+[1+k]≡1+k → 1+k≢k (suc-injective 1+[1+k]≡1+k)) n

caseNat-extract-zero : ∀ {l} {A : Set l} (z s : A) n →
  z ≢ s →
  caseNat z s n ≡ z → n ≡ zero
caseNat-extract-zero z s n z≢s = ind (λ k → caseNat z s k ≡ z → k ≡ zero)
  (λ x → refl)
  (λ k c[z,s,k]≡z→k≡zero c[z,s,suc[k]]≡z → ⊥-elim $ z≢s
    $ trans (sym c[z,s,suc[k]]≡z) (caseNat-step _ _ _) ) n

-- Properties of _+_
+-identityˡ : ∀ n → zero + n ≡ n
+-identityˡ n = rec-base n suc

suc-+ : ∀ m n → suc m + n ≡ suc (m + n)
suc-+ m n = rec-step n suc m

+-identityʳ : ∀ n → n + zero ≡ n
+-identityʳ n₀ = ind (λ n → n + zero ≡ n) (+-identityˡ zero) step n₀
  where
  step : ∀ k → k + zero ≡ k → suc k + zero ≡ suc k
  step k k+zero≡k = begin
    suc k + zero   ≡⟨ suc-+ k zero ⟩
    suc (k + zero) ≡⟨ cong suc k+zero≡k ⟩
    suc k          ∎

+-assoc : ∀ m n o → (m + n) + o ≡ m + (n + o)
+-assoc m₀ n o = ind (λ m → (m + n) + o ≡ m + (n + o)) base step m₀
  where
  base : (zero + n) + o ≡ zero + (n + o)
  base = begin
    (zero + n) + o ≡⟨ cong (_+ o) $ +-identityˡ n ⟩
    n + o          ≡⟨ sym $ +-identityˡ (n + o) ⟩
    zero + (n + o) ∎

  step : ∀ k → (k + n) + o ≡ k + (n + o) → (suc k + n) + o ≡ suc k + (n + o)
  step k [k+n]+o≡k+[n+o] = begin
    (suc k + n) + o   ≡⟨ cong (_+ o) $ suc-+ k n ⟩
    suc (k + n) + o   ≡⟨ suc-+ (k + n) o ⟩
    suc ((k + n) + o) ≡⟨ cong suc [k+n]+o≡k+[n+o] ⟩
    suc (k + (n + o)) ≡⟨ sym $ suc-+ k (n + o) ⟩
    suc k + (n + o)   ∎

suc≡one+ : ∀ n → suc n ≡ one + n
suc≡one+ n = begin
  suc n          ≡⟨ cong suc (sym $ +-identityˡ n) ⟩
  suc (zero + n) ≡⟨ sym $ suc-+ zero n ⟩
  suc zero + n   ∎

+-suc : ∀ m n → m + suc n ≡ suc m + n
+-suc m₀ n = ind (λ m → m + suc n ≡ suc m + n)
   (begin
    zero + suc n   ≡⟨ +-identityˡ (suc n) ⟩
    suc n          ≡⟨ cong suc (sym $ +-identityˡ n) ⟩
    suc (zero + n) ≡⟨ sym $ suc-+ zero n ⟩
    suc zero + n   ∎
    )
  (λ m m+[1+n]≡[1+m]+n → begin
    suc m + suc n   ≡⟨ suc-+ m (suc n) ⟩
    suc (m + suc n) ≡⟨ cong suc m+[1+n]≡[1+m]+n ⟩
    suc (suc m + n) ≡⟨ sym $ suc-+ (suc m) n ⟩
    suc (suc m) + n ∎
    )
  m₀

+-comm : ∀ m n → m + n ≡ n + m
+-comm m₀ n = ind (λ m → m + n ≡ n + m)
  (begin
    zero + n ≡⟨ +-identityˡ n ⟩
    n        ≡⟨ sym $ +-identityʳ n ⟩
    n + zero ∎
    )
  (λ m m+n≡n+m → begin
    suc m + n   ≡⟨ suc-+ m n ⟩
    suc (m + n) ≡⟨ cong suc m+n≡n+m ⟩
    suc (n + m) ≡⟨ sym $ suc-+ n m ⟩
    suc n + m   ≡⟨ sym $ +-suc n m ⟩
    n + suc m   ∎
    )
  m₀

+-cancelˡ-≡ : ∀ m n o → (m + n) ≡ (m + o) → n ≡ o
+-cancelˡ-≡ m n o = ind (λ k → k + n ≡ k + o → n ≡ o)
  (λ zero+n≡zero+o → begin
      n        ≡⟨ sym $ +-identityˡ n ⟩
      zero + n ≡⟨ zero+n≡zero+o ⟩
      zero + o ≡⟨ +-identityˡ o ⟩
      o ∎ )
  (λ k k+n≡k+o→n≡o suck+n≡suck+o → begin
     n ≡⟨ k+n≡k+o→n≡o $ suc-injective $ (begin
        suc (k + n) ≡⟨ sym $ suc-+ k n ⟩
        suc k + n   ≡⟨ suck+n≡suck+o ⟩
        suc k + o   ≡⟨ suc-+ k o ⟩
        suc (k + o) ∎
       ) ⟩
     o ∎ )
  m

+-cancelʳ-≡ : ∀ m n o → (m + n) ≡ (o + n) → m ≡ o
+-cancelʳ-≡ m n o m+n≡o+n = +-cancelˡ-≡ n m o (begin
  n + m ≡⟨ +-comm n m ⟩
  m + n ≡⟨ m+n≡o+n ⟩
  o + n ≡⟨ +-comm o n ⟩
  n + o ∎ )

+-conicalˡ : ∀ m n → m + n ≡ zero → m ≡ zero
+-conicalˡ m n = ind (λ k → k + n ≡ zero → k ≡ zero) (λ _ → refl)
  (λ k k+n≡zero→k≡zero suck+n≡zero →
      ⊥-elim $ z≢s (k + n) $ trans (sym suck+n≡zero) (suc-+ k n)
    ) m

+-conicalʳ : ∀ m n → m + n ≡ zero → n ≡ zero
+-conicalʳ m n m+n≡zero = +-conicalˡ n m (trans (+-comm n m) m+n≡zero)

-- suc[n]≡1+n

-- Order
z≤n : ∀ {n} → zero ≤ n
z≤n {n} = n , +-identityˡ n

s≤s : ∀ {m n} → m ≤ n → suc m ≤ suc n
s≤s {m} {n} (o , m+o≡n) = o , trans (suc-+ m o) (cong suc m+o≡n)

≤-pred : ∀ {m n} → suc m ≤ suc n → m ≤ n
≤-pred {m} {n} (o , sucm+o≡sucn) =
  o , suc-injective (trans (sym $ suc-+ m o) sucm+o≡sucn)

≤-refl : ∀ {n} → n ≤ n
≤-refl {n} = ind (λ n → n ≤ n) z≤n (λ k → s≤s) n

≤-reflexive : ∀ {m n} → m ≡ n → m ≤ n
≤-reflexive {m} {n} m≡n = subst (m ≤_) m≡n (≤-refl {m})

≤-step : ∀ {m n} → m ≤ n → m ≤ suc n
≤-step {m} {n} (o , m+o≡n) = suc o , (begin
  m + suc o   ≡⟨ +-suc m o ⟩
  suc m + o   ≡⟨ suc-+ m o ⟩
  suc (m + o) ≡⟨ cong suc m+o≡n ⟩
  suc n       ∎ )

≤-back : ∀ {m n} → suc m ≤ n → m ≤ n
≤-back {m} {n} (o , suc[m]+o≡n) = suc o , (begin
  m + suc o ≡⟨ +-suc m o ⟩
  suc m + o ≡⟨ suc[m]+o≡n ⟩
  n ∎ )

≤-steps : ∀ {m n} o → m ≤ n → m ≤ o + n
≤-steps {m} {n} o m≤n = ind (λ k → m ≤ k + n)
  (subst (m ≤_) (sym $ +-identityˡ n) m≤n)
  (λ k m≤k+n → subst (m ≤_) (sym $ suc-+ k n) (≤-step m≤k+n)) o

≤-antisym : ∀ {m n} → m ≤ n → n ≤ m → m ≡ n
≤-antisym {m} {n} (o , m+o≡n) (p , n+p≡m) = begin
  m        ≡⟨ sym n+p≡m ⟩
  n + p    ≡⟨ cong (n +_) $ p≡zero ⟩
  n + zero ≡⟨ +-identityʳ n ⟩
  n        ∎
  where
  m≡m+[o+p] : m ≡ m + (o + p)
  m≡m+[o+p] = begin
    m           ≡⟨ sym n+p≡m ⟩
    n + p       ≡⟨ cong (_+ p) $ sym m+o≡n ⟩
    (m + o) + p ≡⟨ +-assoc m o p ⟩
    m + (o + p) ∎
  zero≡o+p : zero ≡ o + p
  zero≡o+p = +-cancelˡ-≡ m zero (o + p) (trans (+-identityʳ m) m≡m+[o+p])
  p≡zero : p ≡ zero
  p≡zero = +-conicalʳ o p (sym zero≡o+p)

≤-trans : ∀ {m n o} → m ≤ n → n ≤ o → m ≤ o
≤-trans {m} {n} {o} (p , m+p≡n) (q , n+q≡o) = (p + q) , (begin
  m + (p + q) ≡⟨ sym $ +-assoc m p q ⟩
  (m + p) + q ≡⟨ cong (_+ q) m+p≡n ⟩
  n + q       ≡⟨ n+q≡o ⟩
  o           ∎ )

n≤zero⇒n≡zero : ∀ {n} → n ≤ zero → n ≡ zero
n≤zero⇒n≡zero {n} (o , n+o≡zero) = +-conicalˡ n o n+o≡zero

-- +-mono-≤

zero<suc[n] : ∀ n → zero < suc n
zero<suc[n] n = s≤s z≤n

s<s : ∀ {m n} → m < n → suc m < suc n
s<s = s≤s

<-pred : ∀ {m n} → suc m < suc n → m < n
<-pred = ≤-pred

n≮zero : ∀ n → n ≮ zero
n≮zero n (m , sucn+m≡zero) = s≢z (n + m) $ trans (sym $ suc-+ n m) sucn+m≡zero

≤⇒≯ : ∀ {m n} → m ≤ n → m ≯ n
≤⇒≯  {m} {n} (o , m+o≡n) (p , suc[n]+p≡m) =
  s≢z (p + o) $ +-cancelˡ-≡ n (suc (p + o)) zero $ begin
  n + suc (p + o) ≡⟨ +-suc n (p + o) ⟩
  suc n + (p + o) ≡⟨ sym $ +-assoc (suc n) p o ⟩
  suc n + p + o   ≡⟨ cong (_+ o) $ suc[n]+p≡m ⟩
  m + o           ≡⟨ m+o≡n ⟩
  n               ≡⟨ sym $ +-identityʳ n ⟩
  n + zero        ∎

<⇒≱ : ∀ {m n} → m < n → m ≱ n
<⇒≱ {m} {n} m<n n≤m = ≤⇒≯ n≤m m<n

n≮n : ∀ n → n ≮ n
n≮n n (m , sucn+m≡n) = z≢s m $ +-cancelˡ-≡ n zero (suc m) (begin
  n + zero  ≡⟨ +-identityʳ n ⟩
  n         ≡⟨ sym sucn+m≡n ⟩
  suc n + m ≡⟨ sym $ +-suc n m ⟩
  n + suc m ∎ )

<⇒≢ : ∀ {m n} → m < n → m ≢ n
<⇒≢ {m} {n} m<n m≡n = n≮n m (subst (m <_) (sym m≡n) m<n)

>⇒≢ : ∀ {m n} → m > n → m ≢ n
>⇒≢ {m} {n} m>n m≡n = <⇒≢ m>n (sym m≡n)

≤⇒<∨≡ : ∀ {m n} → m ≤ n → m < n ⊎ m ≡ n
≤⇒<∨≡ {m} {n} (o , m+o≡n) =
  ind (λ k → m + k ≡ n → m < n ⊎ m ≡ n)
      (λ m+zero≡n → inj₂ (trans (sym $ +-identityʳ m) m+zero≡n))
      (λ k _ m+suc[k]≡n → inj₁ (k , (begin
        suc m + k ≡⟨ sym $ +-suc m k ⟩
        m + suc k ≡⟨ m+suc[k]≡n ⟩
        n ∎ )))
      o m+o≡n

<⇒≤ : ∀ {m n} → m < n → m ≤ n
<⇒≤ = ≤-back

n<suc[n] : ∀ n → n < suc n
n<suc[n] n = ≤-refl

<-step : ∀ {m} {n} → m < n → m < suc n
<-step {m} {n} m<n = ≤-step m<n

n∸zero≡n : ∀ n → n ∸ zero ≡ n
n∸zero≡n n = rec-base _ _

<⇒≯ : ∀ {m n} → m < n → m ≯ n
<⇒≯ {m} {n} m<n = ≤⇒≯ (<⇒≤ m<n)

m∸suc[n]≡pred[m∸n] : ∀ m n → m ∸ suc n ≡ pred (m ∸ n)
m∸suc[n]≡pred[m∸n] m n = rec-step _ _ _

zero∸n≡zero : ∀ n → zero ∸ n ≡ zero
zero∸n≡zero =
  ind (λ n → zero ∸ n ≡ zero) (n∸zero≡n zero)
      λ k zero∸k≡zero → (begin
        zero ∸ suc k    ≡⟨ m∸suc[n]≡pred[m∸n] zero k ⟩
        pred (zero ∸ k) ≡⟨ cong pred zero∸k≡zero ⟩
        pred zero       ≡⟨ pred-zero ⟩
        zero            ∎ )

suc[m]∸suc[n]≡m∸n : ∀ m n → suc m ∸ suc n ≡ m ∸ n
suc[m]∸suc[n]≡m∸n m =
  ind (λ n → suc m ∸ suc n ≡ m ∸ n)
      (begin
        suc m ∸ suc zero    ≡⟨ m∸suc[n]≡pred[m∸n] (suc m) zero ⟩
        pred (suc m ∸ zero) ≡⟨ cong pred (n∸zero≡n (suc m)) ⟩
        pred (suc m)        ≡⟨ pred-suc m ⟩
        m                   ≡⟨ sym $ n∸zero≡n m ⟩
        m ∸ zero            ∎ )
      λ k suc[m]∸suc[k]≡m∸k → begin
          suc m ∸ suc (suc k)  ≡⟨ m∸suc[n]≡pred[m∸n] (suc m) (suc k) ⟩
          pred (suc m ∸ suc k) ≡⟨ cong pred suc[m]∸suc[k]≡m∸k ⟩
          pred (m ∸ k)         ≡⟨ sym $ m∸suc[n]≡pred[m∸n] m k ⟩
          m ∸ suc k            ∎

m+n∸m≡n : ∀ m n → m + n ∸ m ≡ n
m+n∸m≡n m n =
  ind (λ k → (k + n) ∸ k ≡ n)
      (begin
        (zero + n) ∸ zero ≡⟨ cong (_∸ zero) $ +-identityˡ n ⟩
        n ∸ zero          ≡⟨ n∸zero≡n n ⟩
        n                 ∎)
      (λ k k+n∸k≡n → begin
          suc k + n ∸ suc k   ≡⟨ cong (_∸ suc k) $ suc-+ k n ⟩
          suc (k + n) ∸ suc k ≡⟨ suc[m]∸suc[n]≡m∸n (k + n) k ⟩
          k + n ∸ k           ≡⟨ k+n∸k≡n ⟩
          n                   ∎
        )
      m

m≤n⇒m+[n∸m]≡n : ∀ {m n} → m ≤ n → m + (n ∸ m) ≡ n
m≤n⇒m+[n∸m]≡n {m} {n} (o , m+o≡n) = begin
  m + (n ∸ m)     ≡⟨ cong (λ v → m + (v ∸ m)) (sym m+o≡n) ⟩
  m + (m + o ∸ m) ≡⟨ cong (m +_) $ m+n∸m≡n m o ⟩
  m + o           ≡⟨ m+o≡n ⟩
  n               ∎

m∸[m+n]≡zero : ∀ m n → m ∸ (m + n) ≡ zero
m∸[m+n]≡zero m n =
  ind (λ k → k ∸ (k + n) ≡ zero) (zero∸n≡zero (zero + n))
      (λ k k∸[k+n]≡zero → begin
        suc k ∸ (suc k + n) ≡⟨ cong (suc k ∸_) $ suc-+ k n ⟩
        suc k ∸ suc (k + n) ≡⟨ suc[m]∸suc[n]≡m∸n k (k + n) ⟩
        k ∸ (k + n)         ≡⟨ k∸[k+n]≡zero ⟩
        zero                ∎ ) m

m≤n⇒m∸n≡zero : ∀ {m n} → m ≤ n → m ∸ n ≡ zero
m≤n⇒m∸n≡zero {m} {n} (o , m+o≡n) = begin
  m ∸ n       ≡⟨ cong (m ∸_) (sym m+o≡n) ⟩
  m ∸ (m + o) ≡⟨ m∸[m+n]≡zero m o ⟩
  zero        ∎

pred[n]≡zero⇒n≡zero∨n≡one : ∀ n → pred n ≡ zero → n ≡ zero ⊎ n ≡ one
pred[n]≡zero⇒n≡zero∨n≡one =
  ind (λ n → pred n ≡ zero → n ≡ zero ⊎ n ≡ suc zero)
      (λ _ → inj₁ refl)
      λ k pred[k]≡zero→k≡zero∨k≡one pred[suc[k]]≡zero → inj₂
      (cong suc (trans (sym $ pred-suc k) pred[suc[k]]≡zero))

pred[m]≡suc[n]⇒m≡suc[suc[n]] : ∀ {m n} → pred m ≡ suc n → m ≡ suc (suc n)
pred[m]≡suc[n]⇒m≡suc[suc[n]] {m} {n} =
  ind (λ k → pred k ≡ suc n → k ≡ suc (suc n))
      (λ pred[zero]≡suc[n] → ⊥-elim $ z≢s n $ trans (sym pred-zero) pred[zero]≡suc[n] )
      (λ k _ pred[suc[k]]≡suc[n] →
          cong suc (trans (sym $ pred-suc k) pred[suc[k]]≡suc[n]))
      m

≤⇒≤ᵇ : ∀ {m n} → m ≤ n → m ≤ᵇ n ≡ true
≤⇒≤ᵇ {m} {n} (o , m+o≡n) = begin
  caseNat true false (m ∸ n)
    ≡⟨ cong (λ v → caseNat true false (m ∸ v)) $ sym m+o≡n ⟩
  caseNat true false (m ∸ (m + o))
    ≡⟨ cong (caseNat true false) $ m∸[m+n]≡zero m o ⟩
  caseNat true false zero
    ≡⟨ caseNat-base true false ⟩
  true
    ∎

data Order (m n : N) : Set a where
  lt : (m<n : m < n) → Order m n
  eq : (m≡n : m ≡ n) → Order m n
  gt : (m>n : m > n) → Order m n

private
  order?-zero : ∀ n → Order zero n
  order?-zero = ind (λ n → Order zero n) (eq refl) λ k _ → lt (zero<suc[n] k)

  order?-suc : ∀ n k → Order k n → Order (suc k) n
  order?-suc n k (lt k<n) with ≤⇒<∨≡ k<n
  ... | inj₁ suc[k]<n     = lt suc[k]<n
  ... | inj₂ suc[k]≡n     = eq suc[k]≡n
  order?-suc n k (eq k≡n) = gt (subst (_< suc k) k≡n $ n<suc[n] k)
  order?-suc n k (gt k>n) = gt (<-step k>n)

order? : ∀ m n → Order m n
order? m₀ n₀ =
  ind (λ k → Order k n₀) (order?-zero n₀) (λ k → order?-suc n₀ k) m₀

_≟_ : ∀ m n → Dec (m ≡ n)
m ≟ n with order? m n
... | lt m<n = no (<⇒≢ m<n)
... | eq m≡n = yes m≡n
... | gt m>n = no (>⇒≢ m>n)

≡-irrelevant : ∀ {m n : N} (p q : m ≡ n) → p ≡ q
≡-irrelevant = M.≡-irrelevant
  where module M = Decidable⇒UIP _≟_

≤-irrelevant : ∀ {m n : N} (p q : m ≤ n) → p ≡ q
≤-irrelevant {m} {n} (o , m+o≡n) (p , m+p≡n)
  with +-cancelˡ-≡ m o p (trans m+o≡n (sym m+p≡n))
... | refl = cong (o ,_) (≡-irrelevant m+o≡n m+p≡n)

≤-proj₁-≡ : ∀ {m n : N} (p q : m ≤ n) → proj₁ p ≡ proj₁ q
≤-proj₁-≡ p q = Prodₚ.,-injectiveˡ (≤-irrelevant p q)

≰⇒> : ∀ {m n} → m ≰ n → m > n
≰⇒> {m} {n} m≰n with order? m n
... | lt m<n = ⊥-elim $ m≰n (<⇒≤ m<n)
... | eq m≡n = ⊥-elim $ m≰n (≤-reflexive m≡n)
... | gt m>n = m>n

≮⇒≥ : ∀ {m n} → m ≮ n → m ≥ n
≮⇒≥ {m} {n} m≮n with order? m n
... | lt m<n = ⊥-elim $ m≮n m<n
... | eq m≡n = ≤-reflexive (sym m≡n)
... | gt m>n = <⇒≤ m>n

_≤?_ : ∀ m n → Dec (m ≤ n)
m ≤? n with order? m n
... | lt m<n = yes (<⇒≤ m<n)
... | eq m≡n = yes (≤-reflexive m≡n)
... | gt m>n = no λ m≤n → ≤⇒≯ m≤n m>n

_<?_ : ∀ m n → Dec (m < n)
m <? n with order? m n
... | lt m<n = yes m<n
... | eq m≡n = no λ m<n → <⇒≢ m<n m≡n
... | gt m>n = no λ m<n → <⇒≯ m<n m>n

≤∧≢⇒< : ∀ {m n} → m ≤ n → m ≢ n → m < n
≤∧≢⇒< {m} {n} m≤n m≢n with order? m n
... | lt m<n = m<n
... | eq m≡n = ⊥-elim $ m≢n m≡n
... | gt m>n = ⊥-elim $ ≤⇒≯ m≤n m>n

private
  subst-refl : ∀ {a b} {A : Set a} (B : A → Set b) {x : A} (y : B x) →
               subst B refl y ≡ y
  subst-refl _ _ = refl

  subst-app : ∀ {a b} {A : Set a} {B : A → Set b}
              (f : (x : A) → B x) {x y} (x≡y : x ≡ y) → subst B x≡y (f x) ≡ f y
  subst-app f refl = refl

  subst-cong-app : ∀ {a b c} {A : Set a} {B : Set b} {C : B → Set c}
                   (g : A → B) (f : (x : A) → C (g x)) {x y} (x≡y : x ≡ y) →
                   subst C (cong g x≡y) (f x) ≡ f y
  subst-cong-app {C = C} g f {x} {y} x≡y = begin
    subst C (cong g x≡y) (f x) ≡⟨ sym $ subst-∘ x≡y ⟩
    subst (C ∘ g) x≡y (f x)    ≡⟨ subst-app f x≡y ⟩
    f y                        ∎

  subst-other : ∀ {a b} {A : Set a} {B : A → Set b}
                (f : (x : A) → B x) {x y z} (x≡z : x ≡ z) (y≡z : y ≡ z) →
                subst B x≡z (f x) ≡ subst B y≡z (f y)
  subst-other _ refl refl = refl

  subst-other-g : ∀ {a b c} {A : Set a} {B : Set b} {C : B → Set c} →
                  B.Irrelevant (_≡_ {A = B}) →
                  ∀ (g : A → B) (f : (x : A) → C (g x))
                  {x y z} (x≡y : x ≡ y) (gx≡z : g x ≡ z) (gy≡z : g y ≡ z) →
                  subst C gx≡z (f x) ≡ subst C gy≡z (f y)
  subst-other-g B-irrelevant g f refl refl gy≡z with B-irrelevant gy≡z refl
  subst-other-g B-irrelevant g f refl refl .refl | refl = refl

  -- variant of subst-application
  subst-lemma : ∀ {a₁ a₂ b₁ b₂} {A₁ : Set a₁} {A₂ : Set a₂}
                  {B₁ : A₁ → Set b₁} {B₂ : A₂ → Set b₂}
                  (f : A₁ → A₂) (g : ∀ x → B₁ x → B₂ (f x))
                  {x₁ x₂ : A₁} (x₁≡x₂ : x₁ ≡ x₂) {y : B₁ x₁} →
                  subst B₂ (cong f x₁≡x₂) (g x₁ y) ≡ g x₂ (subst B₁ x₁≡x₂ y)
  subst-lemma _ _ refl = refl

module _ {p} (P : N → N → Set p) where
  inddiag-< :
    (∀ n → P zero (suc n)) → (∀ m n → P m n → P (suc m) (suc n)) →
    ∀ m o → P m (suc m + o)
  inddiag-< Pzs Pss m o =
    ind (λ k → P k (suc k + o))
        (subst (P zero) (suc≡one+ o) (Pzs o))
        (λ k P[k,suc[k]+o] → subst (P (suc k)) (sym $ suc-+ (suc k) o)
          $ Pss k (suc k + o) P[k,suc[k]+o]) m

  inddiag-≡ : P zero zero → (∀ m n → P m n → P (suc m) (suc n)) → ∀ n → P n n
  inddiag-≡ Pzz Pss n = ind (λ k → P k k) Pzz (λ k Pkk → Pss k k Pkk) n

  inddiag-> :
    (∀ n → P (suc n) zero) → (∀ m n → P m n → P (suc m) (suc n)) →
    ∀ n o → P (suc n + o) n
  inddiag-> Psz Pss n o =
    ind (λ k → P (suc k + o) k)
        (subst (λ k → P k zero) (suc≡one+ o) (Psz o))
        (λ k P[suc[k]+o,k] → subst (λ v → P v (suc k)) (sym $ suc-+ (suc k) o)
          (Pss (suc k + o) k P[suc[k]+o,k]))
        n

  -- diagonal induction
  inddiag :
    P zero zero →
    (∀ n → P zero (suc n)) →
    (∀ m → P (suc m) zero) →
    (∀ m n → P m n → P (suc m) (suc n)) →
    ∀ m n → P m n
  inddiag P-zz P-zs P-sz P-ss m n with order? m n
  ... | lt (o , suc[m]+o≡n) = subst (P m) suc[m]+o≡n (inddiag-< P-zs P-ss m o)
  ... | eq m≡n              = subst (P m) m≡n (inddiag-≡ P-zz P-ss m)
  ... | gt (o , suc[n]+o≡m) =
    subst (λ k → P k n) suc[n]+o≡m (inddiag-> P-sz P-ss n o)

  inddiag-zz : ∀ Pzz Pzs Psz Pss → inddiag Pzz Pzs Psz Pss zero zero ≡ Pzz
  inddiag-zz Pzz Pzs Psz Pss with order? zero zero
  ... | lt m<n = ⊥-elim $ n≮n zero m<n
  ... | eq m≡n = begin
    subst (P zero) m≡n (ind (λ k → P k k) Pzz (λ k → Pss k k) zero)
      ≡⟨ cong (λ v → subst (P zero) v _ ) (≡-irrelevant m≡n refl) ⟩
    subst (P zero) refl (ind (λ k → P k k) Pzz (λ k → Pss k k) zero)
      ≡⟨ subst-refl (P zero) (ind (λ k → P k k) Pzz (λ k → Pss k k) zero) ⟩
    ind (λ k → P k k) Pzz (λ k → Pss k k) zero
      ≡⟨ ind-base _ _ _ ⟩
    Pzz
      ∎
  ... | gt m>n = ⊥-elim $ n≮n zero m>n

  inddiag-zs : ∀ Pzz Pzs Psz Pss n → inddiag Pzz Pzs Psz Pss zero (suc n) ≡ Pzs n
  inddiag-zs Pzz Pzs Psz Pss n with order? zero (suc n)
  ... | lt (o , one+o≡suc[n]) = begin
    subst (P zero) one+o≡suc[n] (inddiag-< Pzs Pss zero o)
      ≡⟨ cong (subst (P zero) one+o≡suc[n]) $ ind-base _ _ _ ⟩
    subst (P zero) one+o≡suc[n] (subst (P zero) (suc≡one+ o) (Pzs o))
      ≡⟨ subst-subst (suc≡one+ o) ⟩ -- suc o -> one + o -> suc n
    subst (P zero) so≡sn (Pzs o)
      ≡⟨ cong (λ v → subst (P zero) v (Pzs o)) $ ≡-irrelevant so≡sn (cong suc o≡n) ⟩
    subst (P zero) (cong suc o≡n) (Pzs o)
      ≡⟨ subst-cong-app suc Pzs o≡n ⟩
    Pzs n
      ∎
    where
    so≡sn : suc o ≡ suc n
    so≡sn = trans (suc≡one+ o) one+o≡suc[n]
    o≡n : o ≡ n
    o≡n = suc-injective so≡sn
  ... | eq m≡n = ⊥-elim $ z≢s n m≡n
  ... | gt m>n = ⊥-elim $ n≮zero (suc n) m>n

  inddiag-sz : ∀ Pzz Pzs Psz Pss m → inddiag Pzz Pzs Psz Pss (suc m) zero ≡ Psz m
  inddiag-sz Pzz Pzs Psz Pss m with order? (suc m) zero
  ... | lt m<n = ⊥-elim $ n≮zero (suc m) m<n
  ... | eq m≡n = ⊥-elim $ s≢z m m≡n
  ... | gt (o , one+o≡suc[m]) = begin
    subst (λ k → P k zero) one+o≡suc[m] (inddiag-> Psz Pss zero o)
      ≡⟨ cong (subst (λ k → P k zero) one+o≡suc[m]) $ ind-base _ _ _ ⟩
    subst (λ k → P k zero) one+o≡suc[m] (subst (λ k → P k zero) (suc≡one+ o) (Psz o))
      ≡⟨ subst-subst (suc≡one+ o) ⟩
    subst (λ k → P k zero) so≡sm (Psz o)
      ≡⟨ cong (λ v → subst (λ k → P k zero) v (Psz o)) $ ≡-irrelevant so≡sm (cong suc o≡m) ⟩
    subst (λ k → P k zero) (cong suc o≡m) (Psz o)
      ≡⟨ subst-cong-app suc Psz o≡m ⟩
    Psz m
      ∎
    where
    so≡sm = trans (suc≡one+ o) one+o≡suc[m]
    o≡m = suc-injective so≡sm

  inddiag-ss : ∀ Pzz Pzs Psz Pss m n →
    inddiag Pzz Pzs Psz Pss (suc m) (suc n) ≡
    Pss m n (inddiag Pzz Pzs Psz Pss m n)
  inddiag-ss Pzz Pzs Psz Pss m n with order? (suc m) (suc n) | order? m n
  ... | lt sm<sn@(o , ssm+o≡sn) | lt m<n@(p , sm+p≡n) =
    begin
    subst (P (suc m)) ssm+o≡sn (inddiag-< Pzs Pss (suc m) o)
      ≡⟨ cong (subst (P (suc m)) ssm+o≡sn) $ ind-step _ _ _ m ⟩
    subst (P (suc m)) ssm+o≡sn (subst (P (suc m)) (sym $ suc-+ (suc m) o) $
      Pss m (suc m + o) (inddiag-< Pzs Pss m o))
      ≡⟨ subst-subst (sym $ suc-+ (suc m) o) ⟩
    subst (P (suc m)) suc[sm+o]≡sn
      (Pss m (suc m + o) (inddiag-< Pzs Pss m o))
      ≡⟨ cong (λ v → subst (P (suc m)) v (Pss m (suc m + o) (inddiag-< Pzs Pss m o))) $
           ≡-irrelevant suc[sm+o]≡sn (cong suc sm+o≡n) ⟩
    subst (P (suc m)) (cong suc sm+o≡n) (Pss m (suc m + o) (inddiag-< Pzs Pss m o))
      ≡⟨ subst-lemma suc (Pss m) sm+o≡n ⟩
    Pss m n (subst (P m) sm+o≡n (inddiag-< Pzs Pss m o))
      ≡⟨ cong (Pss m n) $ subst-other-g ≡-irrelevant (suc m +_) (inddiag-< Pzs Pss m) o≡p sm+o≡n sm+p≡n ⟩
    Pss m n (subst (P m) sm+p≡n (inddiag-< Pzs Pss m p))
      ∎
    where
    suc[sm+o]≡sn : suc (suc m + o) ≡ suc n
    suc[sm+o]≡sn = trans (sym $ suc-+ (suc m) o) ssm+o≡sn
    sm+o≡n : suc m + o ≡ n
    sm+o≡n = suc-injective suc[sm+o]≡sn
    o≡p : o ≡ p
    o≡p = ≤-proj₁-≡ (<-pred sm<sn) m<n
  ... | lt sm<sn | eq m≡n = ⊥-elim $ <⇒≢ (<-pred sm<sn) m≡n
  ... | lt sm<sn | gt m>n = ⊥-elim $ <⇒≯ (<-pred sm<sn) m>n
  ... | eq sm≡sn | lt m<n = ⊥-elim $ <⇒≢ m<n (suc-injective sm≡sn)
  ... | eq sm≡sn | eq m≡n = begin
    subst (P (suc m)) sm≡sn (i (suc m))
      ≡⟨ cong (subst (P (suc m)) sm≡sn) $ ind-step _ _ _ m ⟩
    subst (P (suc m)) sm≡sn (Pss m m (i m))
      ≡⟨ cong (λ v → subst (P (suc m)) v (Pss m m (i m))) $ ≡-irrelevant sm≡sn (cong suc m≡n) ⟩
    subst (P (suc m)) (cong suc m≡n) (Pss m m (i m))
      ≡⟨ subst-lemma suc (Pss m) m≡n ⟩
    Pss m n (subst (P m) m≡n (i m))
      ∎
      where
      i = ind (λ k → P k k) Pzz (λ k → Pss k k)
  ... | eq sm≡sn | gt m>n = ⊥-elim $ >⇒≢ m>n (suc-injective sm≡sn)
  ... | gt sm>sn | lt m<n = ⊥-elim $ <⇒≯ (<-pred sm>sn) m<n
  ... | gt sm>sn | eq m≡n = ⊥-elim $ >⇒≢ (<-pred sm>sn) m≡n
  ... | gt sm>sn@(o , ssn+o≡sm) | gt m>n@(p , sn+p≡m) = begin
    subst B₁ ssn+o≡sm (inddiag-> Psz Pss (suc n) o)
      ≡⟨ cong (subst B₁ ssn+o≡sm) $ ind-step _ _ _ n ⟩
    subst B₁ ssn+o≡sm (subst B₁ (sym $ suc-+ (suc n) o) (Pss (suc n + o) n u))
      ≡⟨ subst-subst (sym $ suc-+ (suc n) o) ⟩
    subst B₁ suc[sn+o]≡sm (Pss (suc n + o) n u)
      ≡⟨ cong (λ v → subst B₁ v (Pss (suc n + o) n u)) $ ≡-irrelevant suc[sn+o]≡sm (cong suc sn+o≡m) ⟩
    subst B₁ (cong suc sn+o≡m) (Pss (suc n + o) n u)
      ≡⟨ subst-lemma suc (λ k → Pss k n) sn+o≡m ⟩
    Pss m n (subst B₂ sn+o≡m (inddiag-> Psz Pss n o))
      ≡⟨ cong (Pss m n) $ subst-other-g ≡-irrelevant (suc n +_) (inddiag-> Psz Pss n) o≡p sn+o≡m sn+p≡m ⟩
    Pss m n (subst B₂ sn+p≡m (inddiag-> Psz Pss n p))
      ∎
    where
    B₁ = λ k → P k (suc n)
    B₂ = λ k → P k n
    u = inddiag-> Psz Pss n o
    suc[sn+o]≡sm : suc (suc n + o) ≡ suc m
    suc[sn+o]≡sm = trans (sym $ suc-+ (suc n) o) ssn+o≡sm
    sn+o≡m = suc-injective suc[sn+o]≡sm
    o≡p : o ≡ p
    o≡p = ≤-proj₁-≡ (<-pred sm>sn) m>n
