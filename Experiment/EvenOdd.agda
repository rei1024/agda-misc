{-# OPTIONS --without-K --safe #-}
module Experiment.EvenOdd where

open import Data.List
open import Data.List.Relation.Unary.All
open import Data.Product hiding (map)
open import Data.Sum as Sum hiding (map)
open import Data.Nat
open import Data.Nat.GeneralisedArithmetic
import Data.Nat.Properties as ℕₚ
open import Function.Base
open import Relation.Binary.PropositionalEquality

data RoseTree {a} (A : Set a) : Set a where
  node : A → List (RoseTree A) → RoseTree A

unnode : ∀ {a} {A : Set a} → RoseTree A → A × List (RoseTree A)
unnode (node x rs) = x , rs

foldRoseTree : ∀ {a b} {A : Set a} {B : Set b} →
               (A → List B → B) → RoseTree A → B
foldRoseTrees : ∀ {a b} {A : Set a} {B : Set b} →
                (A → List B → B) → List (RoseTree A) → List B
foldRoseTree f (node x rs) = f x (foldRoseTrees f rs)
foldRoseTrees f []       = []
foldRoseTrees f (x ∷ rs) = foldRoseTree f x ∷ foldRoseTrees f rs

mapRoseTree : ∀ {a b} {A : Set a} {B : Set b} →
              (A → B) → RoseTree A → RoseTree B
mapRoseTree f r = foldRoseTree (λ x rs → node (f x) rs) r

data Parity : Set where
  even odd : Parity

data Pos : Set where
  one  : Pos
  node : Parity → Pos → List Pos → Pos

op : Parity → Parity
op even = odd
op odd  = even

induction : ∀ {p} {P : Pos → Set p} →
            P one →
            (∀ pa x xs → P x → All P xs → P (node pa x xs)) →
            ∀ n → P n
induction-node : ∀ {p} {P : Pos → Set p} →
                 P one →
                 (∀ pa x xs → P x → All P xs → P (node pa x xs)) →
                 ∀ ns → All P ns
induction P1 Pn one            = P1
induction P1 Pn (node pa n ns) = Pn pa n ns (induction P1 Pn n) (induction-node P1 Pn ns)
induction-node P1 Pn []       = []
induction-node P1 Pn (x ∷ ns) = induction P1 Pn x ∷ induction-node P1 Pn ns

recursion : ∀ {a} {A : Set a} → A → (Parity → A → List A → A) → Pos → A
recursion o n p = induction o (λ pa _ _ x AllAxs → n pa x (reduce id AllAxs)) p

ℕ⁺ : Set
ℕ⁺ = Σ ℕ (λ n → n ≢ 0)

1ℕ⁺ : ℕ⁺
1ℕ⁺ = 1 , (λ ())

2ℕ⁺ : ℕ⁺
2ℕ⁺ = 2 , (λ ())

sucℕ⁺ : ℕ⁺ → ℕ⁺
sucℕ⁺ (n , _) = suc n , λ ()

_+ℕ⁺_ : ℕ⁺ → ℕ⁺ → ℕ⁺
(m , m≢0) +ℕ⁺ (n , n≢0) = (m + n) , (λ m+n≡0 → m≢0 (ℕₚ.m+n≡0⇒m≡0 m m+n≡0) )

private
  m*n≡0⇒m≡0∨n≡0 : ∀ m {n} → m * n ≡ 0 → m ≡ 0 ⊎ n ≡ 0
  m*n≡0⇒m≡0∨n≡0 zero    {zero}  m+n≡0 = inj₁ refl
  m*n≡0⇒m≡0∨n≡0 zero    {suc n} m+n≡0 = inj₁ refl
  m*n≡0⇒m≡0∨n≡0 (suc m) {zero}  m+n≡0 = inj₂ refl

_*ℕ⁺_ : ℕ⁺ → ℕ⁺ → ℕ⁺
(m , m≢0) *ℕ⁺ (n , n≢0) =
  (m * n) , λ m*n≡0 → Sum.[ m≢0 , n≢0 ] (m*n≡0⇒m≡0∨n≡0 m m*n≡0)

private
  m^n≡0⇒m≡0 : ∀ m n → m ^ n ≡ 0 → m ≡ 0
  m^n≡0⇒m≡0 zero    (suc n) m^n≡0 = refl
  m^n≡0⇒m≡0 (suc m) (suc n) m^n≡0 with m*n≡0⇒m≡0∨n≡0 (suc m) m^n≡0
  ... | inj₂ sm^n≡0 = m^n≡0⇒m≡0 (suc m) n sm^n≡0

_^ℕ⁺_ : ℕ⁺ → ℕ⁺ → ℕ⁺
(m , m≢0) ^ℕ⁺ (n , n≢0) = (m ^ n) , λ m^n≡0 → m≢0 (m^n≡0⇒m≡0 m n m^n≡0)

_⊓ℕ⁺_ : ℕ⁺ → ℕ⁺ → ℕ⁺
(m , m≢0) ⊓ℕ⁺ (n , n≢0) = (m ⊓ n) , {!   !}

oℕ : ℕ → ℕ
oℕ n = 2 * n

iℕ : ℕ → ℕ
iℕ n = 1 + 2 * n

oℕ⁺ : ℕ⁺ → ℕ⁺
oℕ⁺ n = 2ℕ⁺ *ℕ⁺ n

iℕ⁺ : ℕ⁺ → ℕ⁺
iℕ⁺ n = sucℕ⁺ (2ℕ⁺ *ℕ⁺ n)

o^ℕ⁺ : ℕ⁺ → ℕ⁺ → ℕ⁺
o^ℕ⁺ (m , _) x = fold x oℕ⁺ m

i^ℕ⁺ : ℕ⁺ → ℕ⁺ → ℕ⁺
i^ℕ⁺ (m , _) x = fold x iℕ⁺ m

toℕ⁺ : Pos → ℕ⁺
toℕ⁺ = recursion 1ℕ⁺ f
  where
  f : Parity → ℕ⁺ → List ℕ⁺ → ℕ⁺
  f even x []       = o^ℕ⁺ x 1ℕ⁺
  f even x (y ∷ xs) = o^ℕ⁺ x (f odd y xs)
  f odd  x []       = i^ℕ⁺ x 1ℕ⁺
  f odd  x (y ∷ xs) = i^ℕ⁺ x (f even y xs)
