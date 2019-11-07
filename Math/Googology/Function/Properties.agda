{-# OPTIONS --without-K --safe --exact-split #-}

module Math.Googology.Function.Properties where

-- agda-stdlib
open import Data.Nat
open import Data.Nat.Properties
open import Data.Nat.GeneralisedArithmetic using (fold)
open import Data.List
open import Relation.Binary.PropositionalEquality
open import Function

-- agda-misc
open import Math.Googology.Function

open ≤-Reasoning

------------------------------------------------------------------------
-- Properties of hyperoperation

H-rec : ∀ n a b → H (suc n) a (suc b) ≡ H n a (H (suc n) a b)
H-rec zero          a b = refl
H-rec (suc zero)    a b = refl
H-rec (suc (suc n)) a b = refl

-- H₀ is successor.
H-suc : ∀ a b → H 0 a b ≡ suc b
H-suc a b = refl

-- H₁ is addition.
H-+ : ∀ a b → H 1 a b ≡ a + b
H-+ a 0       = sym $ +-identityʳ a
H-+ a (suc b) = begin-equality
  suc (H 1 a b) ≡⟨ cong suc $ H-+ a b ⟩
  suc (a + b)   ≡⟨⟩
  suc a + b     ≡⟨ sym $ +-suc a b ⟩
  a + suc b     ∎

-- H₂ is multiplication.
H-* : ∀ a b → H 2 a b ≡ a * b
H-* a 0       = sym $ *-zeroʳ a
H-* a (suc b) = begin-equality
  H 1 a (H 2 a b) ≡⟨ cong (H 1 a) $ H-* a b ⟩
  H 1 a (a * b)   ≡⟨ H-+ a (a * b) ⟩
  a + a * b       ≡⟨ sym $ *-suc a b ⟩
  a * suc b       ∎

-- H₃ is exponentiation.
H-^ : ∀ a b → H 3 a b ≡ a ^ b
H-^ a 0       = refl
H-^ a (suc b) = begin-equality
  H 2 a (H 3 a b) ≡⟨ cong (H 2 a) $ H-^ a b ⟩
  H 2 a (a ^ b)   ≡⟨ H-* a (a ^ b) ⟩
  a * (a ^ b)     ∎

-- Hₙ(a, 1) = a  (n ≥ 2)
H[2+n,a,1]≡a : ∀ n a → H (2 + n) a 1 ≡ a
H[2+n,a,1]≡a 0       a = refl
H[2+n,a,1]≡a (suc n) a = begin-equality
  H (suc (suc (suc n))) a 1 ≡⟨ H-rec (suc (suc n)) a 0 ⟩
  H (2 + n) a 1             ≡⟨ H[2+n,a,1]≡a n a ⟩
  a                         ∎

-- a ↑ⁿ 1 ≡ a
a↑ⁿ1≡a : ∀ a n → a ↑[ n ] 1 ≡ a
a↑ⁿ1≡a a n = H[2+n,a,1]≡a n a

-- Hₙ(2, 2) = 4  (n ≥ 1)
H[1+n,2,2]≡4 : ∀ n → H (1 + n) 2 2 ≡ 4
H[1+n,2,2]≡4 0       = refl
H[1+n,2,2]≡4 (suc n) = begin-equality
  H (suc (suc n)) 2 (suc 1)         ≡⟨ H-rec (suc n) 2 1 ⟩
  H (suc n) 2 (H (suc (suc n)) 2 1) ≡⟨ cong (H (suc n) 2) $ H[2+n,a,1]≡a n 2 ⟩
  H (suc n) 2 2                     ≡⟨ H[1+n,2,2]≡4 n ⟩
  4                                 ∎

-- Hₙ(1, b) = 1  (n ≥ 3)
H[3+n,1,b]≡1 : ∀ n b → H (3 + n) 1 b ≡ 1
H[3+n,1,b]≡1 0       b       = trans (H-^ 1 b) (^-zeroˡ b)
H[3+n,1,b]≡1 (suc n) 0       = refl
H[3+n,1,b]≡1 (suc n) (suc b) = H[3+n,1,b]≡1 n (H (4 + n) 1 b)

-- Hₙ(a, a) = H₁₊ₙ(a, 2)  (n ≥ 1)
H[1+n,a,a]≡H[2+n,a,2] : ∀ n a → H (1 + n) a a ≡ H (2 + n) a 2
H[1+n,a,a]≡H[2+n,a,2] n a = sym lemma where
  lemma : H (2 + n) a 2 ≡ H (1 + n) a a
  lemma = begin-equality
    H (suc (suc n)) a 2
      ≡⟨ H-rec (suc n) a 1 ⟩
    H (suc n) a (H (suc (suc n)) a 1)
      ≡⟨ cong (H (suc n) a) $ H[2+n,a,1]≡a n a ⟩
    H (suc n) a a
      ∎

H-is-fold : ∀ n a b → H (3 + n) a b ≡ fold 1 (H (2 + n) a) b
H-is-fold n a 0       = refl
H-is-fold n a (suc b) = cong (H (2 + n) a) $ H-is-fold n a b

H[1+n,2,3]≡H[n,2,4] : ∀ n → H (1 + n) 2 3 ≡ H n 2 4
H[1+n,2,3]≡H[n,2,4] 0       = refl
H[1+n,2,3]≡H[n,2,4] (suc n) = begin-equality
  H (2 + n) 2 3
    ≡⟨ H-rec (1 + n) 2 2 ⟩
  H (1 + n) 2 (H (2 + n) 2 2)
    ≡⟨ cong (H (1 + n) 2) $ H[1+n,2,2]≡4 (1 + n) ⟩
  H (1 + n) 2 4
    ∎

H[2+n,0,1]≡0 : ∀ n → H (2 + n) 0 1 ≡ 0
H[2+n,0,1]≡0 zero    = refl
H[2+n,0,1]≡0 (suc n) = H[2+n,0,1]≡0 n

H[4+n,0,2*b]≡1 : ∀ n b → H (4 + n) 0 (2 * b) ≡ 1
H[4+n,0,1+2*b]≡0 : ∀ n b → H (4 + n) 0 (1 + 2 * b) ≡ 0
H[4+n,0,2*b]≡1 n zero    = refl
H[4+n,0,2*b]≡1 n (suc b) = begin-equality
  H (3 + n) 0 (H (4 + n) 0 (b + (suc (b + 0))))
    ≡⟨ cong (λ v → H (3 + n) 0 (H (4 + n) 0 v)) $ +-suc b (b + 0) ⟩
  H (3 + n) 0 (H (4 + n) 0 (1 + 2 * b))
    ≡⟨ cong (H (3 + n) 0) $ H[4+n,0,1+2*b]≡0 n b ⟩
  H (3 + n) 0 0
    ≡⟨⟩
  1
    ∎
H[4+n,0,1+2*b]≡0 n b = begin-equality
  H (3 + n) 0 (H (4 + n) 0 (2 * b))
    ≡⟨ cong (H (3 + n) 0) $ H[4+n,0,2*b]≡1 n b ⟩
  H (3 + n) 0 1
    ≡⟨ H[2+n,0,1]≡0 (suc n) ⟩
  0
    ∎

------------------------------------------------------------------------
-- Properties of `ack`

private
  ack-H-helper :
    ∀ (P : ℕ → ℕ → Set) → (∀ n → P 0 n) →
    (∀ m → P m 1 → P (suc m) 0) →
    (∀ m n → P (suc m) n → (∀ n′ → P m n′) → P (suc m) (suc n)) → ∀ m n → P m n
  ack-H-helper P P[0,n] P[m,0] P[m,n] = go where
    go : ∀ m n → P m n
    go 0       n       = P[0,n] n
    go (suc m) 0       = P[m,0] m (go m 1)
    go (suc m) (suc n) = P[m,n] m n (go (suc m) n) (go m)

-- Ackermann function can be expressed in terms of hyperoperation.
-- 3 + Ack(m, n) = Hₙ(2, 3 + n)
ack-H : ∀ m n → 3 + ack m n ≡ H m 2 (3 + n)
ack-H = ack-H-helper P (λ _ → refl) P[m,0] P[m,n]
  where
  P : ℕ → ℕ → Set
  P m n = 3 + ack m n ≡ H m 2 (3 + n)

  P[m,0] : ∀ m → P m 1 → P (suc m) 0
  P[m,0] m P[m,1] = trans P[m,1] (sym $ H[1+n,2,3]≡H[n,2,4] m)

  P[m,n] : ∀ m n → P (suc m) n → (∀ n′ → P m n′) → P (suc m) (suc n)
  P[m,n] m n P[m′,n] P[m,n′] = begin-equality
    3 + ack m (ack (1 + m) n)   ≡⟨ P[m,n′] (ack (1 + m) n) ⟩
    H m 2 (3 + ack (1 + m) n)   ≡⟨ cong (H m 2) $ P[m′,n] ⟩
    H m 2 (H (1 + m) 2 (3 + n)) ≡⟨ sym $ H-rec m 2 (3 + n) ⟩
    H (1 + m) 2 (4 + n)         ∎

iter : (ℕ → ℕ) → ℕ → ℕ
iter f 0       = f 1
iter f (suc n) = f (iter f n)

iter-is-fold : ∀ f n → iter f n ≡ fold (f 1) f n
iter-is-fold f zero    = refl
iter-is-fold f (suc n) = cong f (iter-is-fold f n)

ack-is-fold′ : ∀ m n → ack m n ≡ fold suc iter m n
ack-is-fold′ 0       n       = refl
ack-is-fold′ (suc m) 0       = ack-is-fold′ m 1
ack-is-fold′ (suc m) (suc n) = begin-equality
  ack m (ack (suc m) n)
    ≡⟨ ack-is-fold′ m (ack (suc m) n) ⟩
  fold suc iter m (ack (suc m) n)
    ≡⟨ cong (fold suc iter m) $ ack-is-fold′ (suc m) n ⟩
  fold suc iter m (iter (fold suc iter m) n)
    ∎

ack-is-fold : ∀ m n → ack m n ≡ fold suc (λ f n → fold (f 1) f n) m n
ack-is-fold zero    n       = refl
ack-is-fold (suc m) zero    = ack-is-fold m 1
ack-is-fold (suc m) (suc n) =
 trans (ack-is-fold m (ack (suc m) n))
       (cong (fold suc (λ f n → fold (f 1) f n) m) (ack-is-fold (suc m) n))
